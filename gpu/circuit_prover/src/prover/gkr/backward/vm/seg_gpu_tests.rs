//! The GPU parity ladder for the SEGMENTED lean VM.
//!
//! **What is under test.** The fifteen release kernels of
//! `native/prover/gkr/backward/segmented_vm.cu`, driven through
//! [`launch_bwd_seg`] with descriptors [`lower_bwd_seg`] produced from artifacts
//! `gkr_eval_isa`'s own `compile_lean_coordinate` emitted. There is no validation
//! probe in this lineage and no hand-built wire: every program here is a program
//! the production compiler would emit, and every descriptor is one host lowering
//! would build.
//!
//! **The three oracles.** Each cell is checked along the chain §12.4 requires,
//! with two independent CPU references rather than one:
//!
//! ```text
//! semantic CPU  (interpret_coeff_layer, term by term)
//!   == lean CPU (interpret_lean_program at THIS K, the K-split the launch uses)
//!   -> GPU per-row contributions (eq * acc_c0, eq * acc_c2)
//!   -> the reduced (e_partial, c_partial) pair
//!   -> the four round coefficients
//!   -> the challenge and claim after the INCUMBENT round update.
//! ```
//!
//! The incumbent enters at the last two rungs by construction: the reduction and
//! the round update are `mega_finalize` / `ab_backward_sumcheck_round_update_kernel`
//! and the upstream `output_univariate_monomial_form_max_quadratic`, all untouched.
//! Nothing here compares the new lineage only against itself.
//!
//! **What the matrix has to cover, and why.** The axes are not decoration; each one
//! is a kernel path nothing else reaches:
//!
//!   * `K` ∈ {1, 2, 4, 16, 32} — `K = 1` bypasses shared memory entirely,
//!     `K = 2` is the staged epilogue's zero-trip loop, `K = 32` is the maximum
//!     plane. Field addition is exact, so every `K` must give BIT-IDENTICAL sums.
//!   * rounds R0 and D0–D3 — R0 has no prologue and no seed; D1/D2 fold inline in
//!     the eval loop; D2 under `Materialize` and D3 fold in the PROLOGUE and
//!     publish. Both fold paths, at both depths.
//!   * three epilogues — they differ only in shared-memory footprint and barrier
//!     count, and that footprint is the ONE cross-language number nothing compares
//!     at build time ([`bwd_seg_epilogue_smem_bytes`] mirrors the header by hand),
//!     so a mismatch is an out-of-bounds shared access rather than a build error.
//!   * a row count that is not a multiple of 32 — the dead-lane clamp, which keeps
//!     `__syncthreads()` block-uniform in the last tile.
//!   * a nonzero `c_init` — the `K`-triangle alone passes VACUOUSLY at
//!     `c_init = 0`, since a zero seed lands correctly however many partials carry
//!     it.
//!
//! **`--features bench` is REQUIRED**; see [`super`]'s module doc. Every gate below
//! is additionally `#[ignore]`d, so it needs `--ignored` on top of the feature:
//!
//! ```text
//! cargo +nightly-2026-02-10 test -p gpu_circuit_prover --features bench --release --no-run
//! .agents/bin/with_gpu_lock.sh <binary> --exact <test> --ignored --nocapture
//! ```

/// Proof to the always-compiled `super::gating` module that this file was built.
///
/// It is the only thing that distinguishes "the GPU gates passed" from "the GPU
/// gates were never compiled", which a `--features bench`-less run cannot tell
/// apart on its own.
pub(super) const SEG_PARITY_SUITE_COMPILED: bool = true;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;
use std::sync::Arc;

use cs::gkr_compiler::dag_ir::{BwdRegime, FieldKind};
use era_cudart::memory::{memory_copy, memory_copy_async};
use era_cudart::slice::DeviceSlice;
use gkr_eval_isa::bwd::coeff::interp::{interpret_coeff_layer, interpret_lean_program};
use gkr_eval_isa::bwd::coeff::lean::decode_program;
use gkr_eval_isa::bwd::coeff::model::{CoeffLayer, CoefficientRecipeId};

use super::seg::{
    bwd_seg_blocks_per_sm, bwd_seg_claim_point_device_ptr, bwd_seg_coeff_bank_device_ptr,
    bwd_seg_epilogue_smem_bytes, bwd_seg_fold_weights_device_ptr, launch_bwd_seg,
    launch_bwd_seg_build_fold_weights, BwdSegEpilogue,
};
use super::seg_compile::{
    chained_round_storage, download_e4, lean_coordinate, seg_chained_model, seg_claim_point,
    seg_ext, seg_host_model, seg_publish_poison, seg_round_binding, short_name,
    upload_round_storage, E4Deltas, SegCoordinate, SegHostModel, SegResolver, SegRoundStorage,
    SegScratch, ADD_SUB_LAYOUT, SEG_LAYOUTS,
};
use super::seg_desc::{
    BwdSegDesc, BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE, BWD_COEFF_ORIGIN_READ_EXT,
    BWD_COEFF_PROCEDURAL_NONE, BWD_SEG_CONST_BANK, BWD_SEG_FOLD_WEIGHT_SLOTS, BWD_SEG_MAX_K,
};
use super::seg_lower::{
    e4_limbs, lower_bwd_seg, BwdSegLaunchDesc, BwdSegSetup, CoeffMode, D2Policy, ProgramMode,
    SourceClass,
};
use super::seg_lower_tests::expected_fold_weights;
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::STATE_SIZE;
use crate::ops::gkr_ops::backward_sumcheck_round_update;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::WARP_SIZE;
use crate::prover::gkr::backward::{
    get_eq_high_constant_device_ptr, launch_backward_dual_finalize_from_acc, make_eq_sizes,
    GkrEqSizes, GKR_EQ_GROUP_SIZE, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS,
};
use crate::prover::test_utils::make_test_context;
use crate::prover::ProverContext;
use crate::upstream::{Field, Seed};

/// Rows every cell of the main matrix evaluates.
///
/// 200 is SEVEN 32-row tiles with a partial last one (8 live lanes, 24 clamped), so
/// the dead-lane clamp runs in every launch rather than in a special case; and it
/// is `<= MEGA_FINALIZE_BLOCK_THREADS`, which is what lets the incumbent
/// single-launch fused tail reduce the contribution buffer directly.
const SEG_ROWS: usize = 200;

/// The `K` axis. The brief's {4, 16, 32} plus the two shapes only a boundary
/// reaches: `K = 1` (no plane, no barrier — the epilogue's early return) and
/// `K = 2` (the staged epilogue's `for w in 2..k` loop runs zero times).
const SEG_K: [usize; 5] = [1, 2, 4, 16, 32];

/// The largest member of [`SEG_K`] the continuation family can launch.
///
/// The continuation family now reaches the GEOMETRY cap, so this equals
/// [`BWD_SEG_MAX_K`] and the axis has no launchability hole left above it: a
/// 1024-thread block gets 65,536 registers, i.e. 64 per thread, and every
/// continuation symbol of the flat-fold build allocates at most that (the peak is
/// the `accbothsmem` rung at exactly 64; `segmented_vm.cu` still sets no
/// `__launch_bounds__` — spec §15: the natural register count is the measurement).
///
/// It was 16 while the fold was the recursive pyramid and while the unrolled flat
/// fold kept every leaf load live at once (continuation peak 76 and 72 registers
/// respectively — both above 64, so `K = 32` was a legal geometry the compiled
/// kernel could not host and a launch at it failed with
/// `ErrorLaunchOutOfResources`). The rolled flat fold brought the band to 50–64,
/// which is what made the cap reachable.
///
/// `17..=31` is still never PROBED here, but nothing above the cap exists to find:
/// `BWD_SEG_MAX_K` is `32 * k <= 1024`. A sweep over that range is a
/// blocks/SM-versus-`K` performance question, not a launchability one.
///
/// Pinned rather than only derived: it is how far up the axis the continuation cells
/// of the matrix run, so a silent change would silently shrink what the matrix
/// covers. [`bwd_seg_k_ceiling_is_measured_not_assumed`] is where it is measured.
const PINNED_CONT_LARGEST_LAUNCHABLE_PROBED_K: usize = 32;

const _: () = {
    assert!(SEG_K[SEG_K.len() - 1] == BWD_SEG_MAX_K);
    // The clamp path is a PROPERTY of the row count, so it is asserted here rather
    // than described in prose: 200 is not a whole number of tiles.
    assert!(SEG_ROWS % 32 != 0);
};

/// Arena bytes the ladder's synthetic backings need.
///
/// The widest cell is a corpus layer at depth three: every source's column is
/// `2 * rows << 3` elements, and the corpus tops out near a thousand sources.
const SEG_ARENA_BYTES: usize = 8 << 30;

fn make_seg_context() -> ProverContext {
    let block_log = crate::prover::ProverContextConfig::default().allocator_block_log_size;
    make_test_context((SEG_ARENA_BYTES >> block_log).max(1), 64)
}

// ── Device helpers ───────────────────────────────────────────────────────────
//
// Deliberately NOT shared with `gpu_tests`: these are private there, and the whole
// point of the two lineages is that retiring the cell-era one is a deletion. The
// duplication is ~80 lines and it is what keeps this file compiling after that.

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

fn e4_bits(value: E4) -> [u32; 4] {
    // SAFETY: E4 is the pinned four-u32 Rust/CUDA ABI field representation, and this
    // is a read-only reinterpretation for exact comparison and reporting.
    unsafe { std::mem::transmute(value) }
}

#[track_caller]
fn assert_e4(label: &str, got: E4, expected: E4) {
    assert_eq!(e4_bits(got), e4_bits(expected), "{label}");
}

// ── The two `__constant__` symbols a launch depends on ───────────────────────

/// E4 values the `__constant__` `ab_gkr_eq_high` symbol holds.
const EQ_HIGH_SLAB_LEN: usize = GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN;

/// The `__constant__` eq-high slab, as a device slice.
///
/// SAFETY: two things, since this mints a fresh `&'static mut` on every call.
/// Extent: `get_eq_high_constant_device_ptr` returns the address of the
/// `ab_gkr_eq_high` symbol, whose declared extent is exactly [`EQ_HIGH_SLAB_LEN`]
/// E4 values. Aliasing: callers must hold ONE borrow at a time — every call site
/// below passes the result straight into a single `memory_copy*` and drops it.
fn eq_high_slab() -> &'static mut DeviceSlice<E4> {
    unsafe { DeviceSlice::from_raw_parts_mut(get_eq_high_constant_device_ptr(), EQ_HIGH_SLAB_LEN) }
}

/// Owns the staged `ab_gkr_eq_high` sentinel and clears it again on drop.
///
/// The slab is a process-wide `__constant__` symbol only the incumbent factored-eq
/// BUILD kernel writes in production, so a test that stages it and walks away
/// leaves state behind. Restoring zero makes a later omission LOUD: an unstaged
/// inline eq then evaluates to zero and every contribution with it.
struct StagedEqHigh;

impl Drop for StagedEqHigh {
    fn drop(&mut self) {
        // Synchronous on purpose: `Drop` has no stream, and this must land before
        // the next test observes the symbol.
        memory_copy(eq_high_slab(), &[E4::ZERO; EQ_HIGH_SLAB_LEN]).expect("eq high restore");
    }
}

/// The staged factored-eq state every launch of one test reads.
///
/// `make_eq_sizes(GKR_EQ_GROUP_SIZE)` puts all eight bits in the LOW slab, so both
/// high slabs have size zero and `gkr_compute_eq_inline` reads their slot ZERO as a
/// sentinel — which the incumbent build kernel fills with `E::ONE()`. The test
/// writes the same sentinel, so `eq(row) == eq_low[row & (TABLE_LEN - 1)]`. A
/// per-row-VARYING `eq_low` is the point: a constant one would let a kernel that
/// dropped the eq multiply entirely still pass.
struct StagedEq {
    low: Vec<E4>,
    device_low: DeviceAllocation<E4>,
    sizes: GkrEqSizes,
    _guard: StagedEqHigh,
}

impl StagedEq {
    fn at(&self, row: usize) -> E4 {
        self.low[row & (GKR_EQ_GROUP_TABLE_LEN - 1)]
    }
}

fn stage_eq(context: &ProverContext) -> StagedEq {
    let guard = StagedEqHigh;
    memory_copy_async(
        eq_high_slab(),
        &[E4::ONE; EQ_HIGH_SLAB_LEN],
        context.get_exec_stream(),
    )
    .expect("eq high sentinel");
    let low = (0..GKR_EQ_GROUP_TABLE_LEN)
        .map(|slot| seg_ext(0x00e0, slot as u32, 0))
        .collect::<Vec<_>>();
    let device_low = upload(&low, context);
    StagedEq {
        low,
        device_low,
        sizes: make_eq_sizes(GKR_EQ_GROUP_SIZE),
        _guard: guard,
    }
}

/// Slots of `ab_gkr_main_layer_claim_point` this file stages and then clears.
///
/// The symbol is the ONE authority on fold challenges and it is SHARED with the
/// incumbent, so a test that leaves values in it hands them to whatever runs next.
/// Four slots cover every round the ladder reaches (the deepest catch-up at round
/// `r` reads `[r - delta, r)`).
const CLAIM_POINT_SLOTS: usize = 4;

struct StagedClaimPoint;

impl Drop for StagedClaimPoint {
    fn drop(&mut self) {
        // SAFETY: the pointer is the address of `ab_gkr_main_layer_claim_point`,
        // whose declared extent is far past `CLAIM_POINT_SLOTS`; the slice is used
        // for exactly one synchronous copy and dropped.
        let slab = unsafe {
            DeviceSlice::from_raw_parts_mut(bwd_seg_claim_point_device_ptr(), CLAIM_POINT_SLOTS)
        };
        memory_copy(slab, &[E4::ZERO; CLAIM_POINT_SLOTS]).expect("claim point restore");
    }
}

/// Stage the fold challenges this round reads. Enqueued on `exec_stream`, so it is
/// ordered before the launch that follows.
fn stage_claim_point(claim_point: &[E4], context: &ProverContext) {
    assert!(claim_point.len() <= CLAIM_POINT_SLOTS);
    if claim_point.is_empty() {
        return;
    }
    // SAFETY: as in `StagedClaimPoint::drop`; one borrow, one copy.
    let slab = unsafe {
        DeviceSlice::from_raw_parts_mut(bwd_seg_claim_point_device_ptr(), claim_point.len())
    };
    memory_copy_async(slab, claim_point, context.get_exec_stream()).expect("claim point H2D");
}

/// Stage the reserved-inclusive coefficient payload into this lineage's OWN
/// `__constant__` bank. Never `ab_gkr_flat_coefficients`: the two lineages share no
/// symbol.
fn stage_coefficient_bank(payload: &[E4], context: &ProverContext) {
    assert!(
        payload.len() <= BWD_SEG_CONST_BANK,
        "the payload must fit the constant bank; lowering rejects a longer one"
    );
    // SAFETY: the pointer is the address of `ab_gkr_bwd_seg_coeff_bank`, declared
    // with `BWD_SEG_CONST_BANK` E4 slots; the slice covers a prefix of it and is
    // used for exactly one copy.
    let slab =
        unsafe { DeviceSlice::from_raw_parts_mut(bwd_seg_coeff_bank_device_ptr(), payload.len()) };
    memory_copy_async(slab, payload, context.get_exec_stream()).expect("coefficient bank H2D");
}

// ── The incumbent round update ───────────────────────────────────────────────

/// The five things a round update produces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RoundUpdate {
    seed: Seed,
    claim: E4,
    eq_prefactor: E4,
    coeffs: [E4; 4],
    challenge: E4,
}

/// Fixed, non-degenerate round-update input state. `prev_coord` and `eq_prefactor`
/// are both inverted by the round update, so neither may be zero.
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
    let claim = seg_ext(0x00c1, 0, 0);
    let eq_prefactor = seg_ext(0x00c1, 1, 0);
    let prev_coord = seg_ext(0x00c1, 2, 0);
    assert_ne!(prev_coord, E4::ZERO);
    assert_ne!(eq_prefactor, E4::ZERO);
    (seed, claim, eq_prefactor, prev_coord)
}

/// The incumbent CPU round update, exactly as `crate::ops::gkr_ops`'s own parity
/// test runs it: upstream algebra plus the upstream transcript. Nothing in this
/// lineage reimplements it.
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
    memory_copy_async(
        &mut seed.0[..],
        &state.seed[..STATE_SIZE],
        context.get_exec_stream(),
    )
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

/// The incumbent's OTHER round-update entry point: the standalone
/// `ab_backward_sumcheck_round_update_kernel`, fed the reduced pair directly.
/// Running both pins the `(c0, c2) -> (e_partial, c_partial)` mapping to the pair's
/// ORDER in the reduction buffer rather than to one kernel's reading of it.
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

// ── One launch shape ─────────────────────────────────────────────────────────

/// The four axes a launch is specialized on, beyond the round the fixture fixes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SegShape {
    k: usize,
    coeff: CoeffMode,
    prog: ProgramMode,
    epilogue: BwdSegEpilogue,
}

impl SegShape {
    fn inline(k: usize, coeff: CoeffMode) -> Self {
        Self {
            k,
            coeff,
            prog: ProgramMode::Inline,
            epilogue: BwdSegEpilogue::Plane,
        }
    }

    fn with_epilogue(self, epilogue: BwdSegEpilogue) -> Self {
        Self { epilogue, ..self }
    }

    fn label(&self) -> String {
        format!(
            "K{} {:?} {:?} {:?}",
            self.k, self.coeff, self.prog, self.epilogue
        )
    }
}

/// What one launch produced.
struct SegRun {
    /// `2 * rows` values: `eq * acc_c0` then `eq * acc_c2`.
    contributions: Vec<E4>,
    /// The parity buffer the prologue published into, whole.
    published: Vec<E4>,
    /// The incumbent fused tail's reduction plus round update, run straight off the
    /// contribution buffer the release kernel wrote.
    incumbent: RoundUpdate,
    /// The reduced pair, summed host-side from the contribution buffer.
    reduced: (E4, E4),
}

// ── The fixture ──────────────────────────────────────────────────────────────

/// One `(coordinate, round, rows, D2 policy, c_init)` cell: the host model, its
/// uploaded storage, the CPU expectations, and the buffers every launch of it
/// reuses.
///
/// A fixture is built ONCE per cell and run at many shapes. That is not only a
/// speed choice: reusing one uploaded storage and one publish scratch across `K` is
/// what makes "every `K` produces bit-identical sums" a statement about the KERNEL
/// rather than about two independently generated inputs.
struct SegFixture {
    coord: Arc<SegCoordinate>,
    /// The semantic layer, with this cell's `c_init` applied.
    layer: CoeffLayer,
    c_init: Option<CoefficientRecipeId>,
    model: SegHostModel,
    storage: SegRoundStorage,
    /// Shared, because the d3→d4 chain's two fixtures ping-pong through ONE pair of
    /// parity buffers — that sharing IS what the chain gate is about.
    scratch: Rc<SegScratch>,
    table: Vec<(E4, E4)>,
    /// Per row, from `interpret_coeff_layer`.
    semantic: Vec<(E4, E4)>,
    /// Per `K`, from `interpret_lean_program`; filled lazily because the lean oracle
    /// is the only CPU quantity that depends on the split.
    lean: HashMap<usize, Vec<(E4, E4)>>,
    claim_point: Vec<E4>,
    /// `2 * rows` slots, reused by every launch of this cell and re-poisoned before
    /// each one.
    contributions: DeviceAllocation<E4>,
}

impl SegFixture {
    fn build(
        coord: Arc<SegCoordinate>,
        round: u8,
        rows: usize,
        d2: D2Policy,
        c_init: Option<CoefficientRecipeId>,
        context: &ProverContext,
    ) -> Self {
        let model = seg_host_model(&coord, round, rows, d2, E4Deltas::Supported);
        let storage = upload_round_storage(&model, context);
        let scratch = Rc::new(SegScratch::new(&[&model], context));
        Self::finish(coord, model, storage, scratch, c_init, context)
    }

    fn finish(
        coord: Arc<SegCoordinate>,
        model: SegHostModel,
        storage: SegRoundStorage,
        scratch: Rc<SegScratch>,
        c_init: Option<CoefficientRecipeId>,
        context: &ProverContext,
    ) -> Self {
        let mut layer = coord.layer.clone();
        // THE SEED HAS ONE VALUE PER CELL, and it is the LAYER's unless this cell
        // overrides it. `c_init` is a layer property whose value is round-dependent,
        // so it travels on the round binding — and a binding that dropped the
        // layer's own seed would leave the CPU oracles seeding `acc_c0` and the
        // descriptor seeding zero, which is a silent per-row offset rather than a
        // rejection. Deriving both from this one expression is what rules that out.
        let c_init = c_init.or(layer.c_init);
        assert!(
            c_init.is_none() || coord.regime != BwdRegime::R0,
            "R0 lowering drops the spine's scalar addends, so an R0 layer must carry no seed"
        );
        layer.c_init = c_init;
        let table = model.pair_table();
        let resolver = SegResolver {
            table: &table,
            rows: model.rows,
            bank: &model.bank,
        };
        let label = model.label();
        let semantic = (0..model.rows)
            .map(|row| {
                interpret_coeff_layer(&layer, row, &resolver)
                    .unwrap_or_else(|error| panic!("{label}: semantic row {row}: {error:?}"))
            })
            .collect();
        let claim_point = seg_claim_point(model.round);
        let contributions = upload(&vec![E4::ZERO; 2 * model.rows], context);
        Self {
            coord,
            layer,
            c_init,
            model,
            storage,
            scratch,
            table,
            semantic,
            lean: HashMap::new(),
            claim_point,
            contributions,
        }
    }

    fn label(&self) -> String {
        self.model.label()
    }

    /// The lean oracle at this `K`, computed once.
    fn lean(&mut self, k: usize) -> &[(E4, E4)] {
        if !self.lean.contains_key(&k) {
            let resolver = SegResolver {
                table: &self.table,
                rows: self.model.rows,
                bank: &self.model.bank,
            };
            let label = self.label();
            let rows = self.model.rows;
            let program = &self.coord.artifact.program;
            let values = (0..rows)
                .map(|row| {
                    interpret_lean_program(program, &self.layer, row, &resolver, k)
                        .unwrap_or_else(|error| panic!("{label}: lean K{k} row {row}: {error:?}"))
                })
                .collect();
            self.lean.insert(k, values);
        }
        &self.lean[&k]
    }

    /// Lower this cell at one shape against live runtime pointers.
    ///
    /// Separate from [`Self::launch`] so a test can inspect what lowering STAMPED —
    /// the source classes, the resolved seed limbs, the null program pointer — with
    /// no launch in between to blame.
    fn lower_with(&self, shape: SegShape, eq: &StagedEq) -> BwdSegSetup {
        let binding = seg_round_binding(
            &self.model,
            &self.storage,
            &self.claim_point,
            &self.model.bank,
            self.c_init,
            eq.device_low.as_ptr(),
            eq.sizes,
            self.contributions.as_ptr() as *mut E4,
        );
        lower_bwd_seg(
            &self.coord.artifact,
            &binding,
            &self.scratch.resolved(),
            shape.k,
            self.model.d2,
            shape.prog,
            shape.coeff,
        )
        .unwrap_or_else(|error| panic!("{}: {}: lower: {error:?}", self.label(), shape.label()))
    }

    /// Lower, stage, launch, and run the incumbent fused tail over the contribution
    /// buffer the release kernel wrote.
    fn launch(&mut self, shape: SegShape, eq: &StagedEq, context: &ProverContext) -> SegRun {
        let label = format!("{}: {}", self.label(), shape.label());
        let rows = self.model.rows;
        let mut setup = self.lower_with(shape, eq);

        // Poisoned rather than zeroed: a row the launch never stores must be a
        // visibly wrong contribution, not a plausible zero.
        let poison = vec![seg_ext(0xdead, 0, 0); 2 * rows];
        memory_copy_async(
            &mut self.contributions[..2 * rows],
            &poison,
            context.get_exec_stream(),
        )
        .expect("contribution poison");
        // ...and the parity buffer this round PUBLISHES into. Without this, launch
        // two of a fixture reads back launch one's correct publications and a
        // prologue that did nothing passes.
        self.scratch.poison_write_parity(self.model.round, context);
        // Proved, not assumed: read the buffer back BEFORE the launch and require it
        // to be all poison. A re-poison that silently stopped happening — deleted,
        // moved after the launch, aimed at the wrong parity — would restore exactly
        // the stale-publish masking it was added to remove, and every downstream
        // assertion would go on passing. This is the only place that can see it.
        self.assert_write_parity_is_poison(context);

        stage_claim_point(&setup.claim_point, context);
        // The prelude is continuation-only — round 0 has no challenges to fold — and
        // it must be enqueued AFTER the claim point it reads, on the same stream.
        if self.model.round >= 1 {
            launch_bwd_seg_build_fold_weights(u32::from(self.model.round), context)
                .expect("fold-weight prelude");
        }

        // Everything a launch needs beyond the by-value descriptor is the CALLER's
        // to stage, on the same stream, before the launch.
        let coefficients = match shape.coeff {
            CoeffMode::Constant => {
                stage_coefficient_bank(&setup.coefficients, context);
                None
            }
            CoeffMode::DevPtr => Some(upload(&setup.coefficients, context)),
        };
        let program =
            (shape.prog == ProgramMode::DevPtr).then(|| upload(&setup.program_words, context));
        match &mut setup.desc {
            BwdSegLaunchDesc::Inline(desc) => {
                if let Some(bank) = &coefficients {
                    desc.coefficients = bank.as_ptr();
                }
            }
            BwdSegLaunchDesc::ProgPtr(desc) => {
                if let Some(bank) = &coefficients {
                    desc.coefficients = bank.as_ptr();
                }
                let words = program
                    .as_ref()
                    .expect("the progptr family uploads a stream");
                desc.program = words.as_ptr();
            }
        }

        launch_bwd_seg(
            &setup,
            self.coord.regime,
            shape.coeff,
            shape.epilogue,
            context,
        )
        .unwrap_or_else(|error| panic!("{label}: launch: {error:?}"));

        let mut state = round_update_state(context);
        launch_backward_dual_finalize_from_acc(
            self.contributions.as_ptr(),
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
        .unwrap_or_else(|error| panic!("{label}: incumbent fused tail: {error:?}"));

        let contributions = download_e4(&self.contributions, 2 * rows, context);
        let published = self
            .scratch
            .download_write_parity(self.model.round, context);
        let incumbent = download_round_update(&state, context);
        let mut e_partial = E4::ZERO;
        let mut c_partial = E4::ZERO;
        for row in 0..rows {
            e_partial.add_assign(&contributions[row]);
            c_partial.add_assign(&contributions[rows + row]);
        }
        drop(coefficients);
        drop(program);
        SegRun {
            contributions,
            published,
            incumbent,
            reduced: (e_partial, c_partial),
        }
    }

    /// The whole ladder for one shape, from the semantic oracle to the incumbent's
    /// claim and challenge.
    fn assert_shape(&mut self, shape: SegShape, eq: &StagedEq, context: &ProverContext) -> SegRun {
        let run = self.launch(shape, eq, context);
        let name = format!("{}: {}", self.label(), shape.label());
        let rows = self.model.rows;

        // Rung 0: the materialize -> eval publish handshake. Checked FIRST, before
        // anything the eval loop produced: the prologue wrote these bytes and the
        // eval loop read them back IN THE SAME LAUNCH, so a prologue fault would
        // otherwise surface as a wrong contribution with no way to tell the two
        // phases apart.
        self.assert_published(&run, &name);

        // Rung 1-3, per row: the two CPU oracles against each other, then the GPU's
        // eq-weighted pair against them.
        let lean = self.lean(shape.k).to_vec();
        let mut e_partial = E4::ZERO;
        let mut c_partial = E4::ZERO;
        for row in 0..rows {
            let semantic = self.semantic[row];
            assert_e4(
                &format!("{name}: semantic vs lean acc_c0 row {row}"),
                lean[row].0,
                semantic.0,
            );
            assert_e4(
                &format!("{name}: semantic vs lean acc_c2 row {row}"),
                lean[row].1,
                semantic.1,
            );
            let weight = eq.at(row);
            let mut expected_c0 = weight;
            expected_c0.mul_assign(&semantic.0);
            let mut expected_c2 = weight;
            expected_c2.mul_assign(&semantic.1);
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

        // Rung 4: the two halves reduce INDEPENDENTLY, each over its own slice, so a
        // half that leaked into the other shows up here.
        assert_e4(
            &format!("{name}: reduced e_partial"),
            run.reduced.0,
            e_partial,
        );
        assert_e4(
            &format!("{name}: reduced c_partial"),
            run.reduced.1,
            c_partial,
        );

        // Rungs 5-6: the four round coefficients and the state after the round
        // update, against BOTH incumbent entry points.
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
        run
    }

    /// The parity buffer this round is about to publish into holds NOTHING but
    /// poison.
    ///
    /// The pre-condition every publish assertion rests on: `assert_published` reads
    /// a launch's output out of a buffer that persists across the launches of one
    /// fixture, so "the prologue wrote this" and "an earlier launch wrote this" are
    /// the same bytes unless the buffer was cleared in between.
    fn assert_write_parity_is_poison(&self, context: &ProverContext) {
        let before = self
            .scratch
            .download_write_parity(self.model.round, context);
        let poison = seg_publish_poison(usize::from(self.model.round & 1));
        for (slot, value) in before.iter().enumerate() {
            assert_e4(
                &format!(
                    "{}: parity slot {slot} was not re-poisoned before the launch",
                    self.label()
                ),
                *value,
                poison,
            );
        }
    }

    /// Every published `(window, column)`'s region holds exactly the fold the host
    /// model predicts, in the split-halves layout — and every HOLE is untouched.
    ///
    /// Driven by the SOURCE table, not by the window's column count: a window's span
    /// is `[first_column, first_column + widest_offset]` and an unreferenced column
    /// inside it is a hole. The plan reserves a region for a hole (the span is what
    /// makes the addressing a base plus a stride) but no source names it, so nothing
    /// folds it and nothing reads it. Checking holes as if they were published would
    /// be a test bug; checking that they stay POISONED is the real property — it is
    /// what catches a publish stride that walks into the neighbouring column.
    fn assert_published(&self, run: &SegRun, name: &str) {
        let rows = self.model.rows;
        let mut written = vec![false; run.published.len()];
        for &(window, column) in &self.model.slots {
            if !self.model.windows[window].publishes {
                continue;
            }
            let Some(offset) = self.scratch.region_offset(self.model.round, window, column) else {
                panic!("{name}: window {window} publishes but has no region");
            };
            let expected = self.model.published(window, column);
            let got = &run.published[offset..offset + 2 * rows];
            for (slot, value) in expected.iter().enumerate() {
                assert_e4(
                    &format!("{name}: published window {window} column {column} slot {slot}"),
                    got[slot],
                    *value,
                );
                written[offset + slot] = true;
            }
        }
        let poison = seg_publish_poison(usize::from(self.model.round & 1));
        for (slot, value) in run.published.iter().enumerate() {
            if !written[slot] {
                assert_e4(
                    &format!("{name}: parity slot {slot} is a hole and must stay untouched"),
                    *value,
                    poison,
                );
            }
        }
    }

    /// The inline descriptor, for the tests that inspect what lowering stamped.
    fn inline_desc(setup: &BwdSegSetup) -> &BwdSegDesc {
        match &setup.desc {
            BwdSegLaunchDesc::Inline(desc) => desc,
            BwdSegLaunchDesc::ProgPtr(_) => panic!("expected the inline-program descriptor"),
        }
    }

    /// The source classes this cell's lowering assigned, as a set.
    fn source_classes(&self, eq: &StagedEq) -> BTreeSet<u8> {
        let setup = self.lower_with(SegShape::inline(4, CoeffMode::Constant), eq);
        let desc = Self::inline_desc(&setup);
        (0..usize::from(desc.num_sources))
            .map(|slot| desc.source[slot].class)
            .collect()
    }
}

// ── The K ceiling ────────────────────────────────────────────────────────────

/// The `K` values one kernel family can actually LAUNCH, out of [`SEG_K`].
///
/// `BWD_SEG_MAX_K` is a geometry cap (`32 * k <= 1024`), not a promise the compiled
/// kernel can host that block: `__launch_bounds__` is deliberately unset (spec §15
/// — the natural register count is the measurement), so a family whose executor
/// needs more than `65536 / 1024 = 64` registers per thread cannot run a
/// 1024-thread block at all, and the launch fails with
/// `ErrorLaunchOutOfResources`.
///
/// Measured through [`bwd_seg_blocks_per_sm`], which answers ZERO for a geometry the
/// kernel cannot host — and which goes through the LAUNCHER's own symbol table, so
/// the family measured here and the family launched below cannot be different
/// kernels. Restating the fifteen-symbol matrix in this file would break exactly
/// that guarantee.
fn seg_launchable_k(
    regime: BwdRegime,
    prog: ProgramMode,
    coeff: CoeffMode,
    epilogue: BwdSegEpilogue,
) -> Vec<usize> {
    SEG_K
        .into_iter()
        .filter(|&k| {
            bwd_seg_blocks_per_sm(regime, prog, coeff, epilogue, k as u32).expect("occupancy query")
                > 0
        })
        .collect()
}

/// How far up [`SEG_K`] each family can be launched, and why that is not always 32.
///
/// What this measures is the largest launchable member of the PROBED axis, per
/// family — not the family's true ceiling, since `17..=31` is never tried. See
/// [`PINNED_CONT_LARGEST_LAUNCHABLE_PROBED_K`].
///
/// Reported rather than silently applied: a `K` the ladder skips is a `K` nothing
/// proves anything about, and the whole point of the axis is that segmentation is
/// invisible to the value. The assertions pin the CURRENT value per family, so a
/// kernel change that lowers it — or a `__launch_bounds__` that finally raises the
/// continuation family to 32 — is a test failure that has to be read, not a quiet
/// change in what the matrix covers.
#[test]
#[cfg(not(no_cuda))]
#[ignore = "GPU; build unlocked and run the executable under with_gpu_lock.sh"]
#[serial_test::serial]
fn bwd_seg_k_ceiling_is_measured_not_assumed() {
    let _context = make_seg_context();
    let mut r0_largest = usize::MAX;
    let mut cont_largest = usize::MAX;
    for regime in [BwdRegime::R0, BwdRegime::Ext] {
        for coeff in [CoeffMode::Constant, CoeffMode::DevPtr] {
            for epilogue in [
                BwdSegEpilogue::Staged,
                BwdSegEpilogue::Plane,
                BwdSegEpilogue::Wide,
            ] {
                let launchable = seg_launchable_k(regime, ProgramMode::Inline, coeff, epilogue);
                let blocks: Vec<String> = SEG_K
                    .into_iter()
                    .map(|k| {
                        let blocks = bwd_seg_blocks_per_sm(
                            regime,
                            ProgramMode::Inline,
                            coeff,
                            epilogue,
                            k as u32,
                        )
                        .expect("occupancy query");
                        format!("K{k}={blocks}")
                    })
                    .collect();
                eprintln!(
                    "[seg-ladder] {regime:?}/{coeff:?}/{epilogue:?} blocks/SM {} -> launchable {launchable:?}",
                    blocks.join(" ")
                );
                let largest = *launchable.last().expect("some K must be launchable");
                match regime {
                    BwdRegime::R0 => r0_largest = r0_largest.min(largest),
                    BwdRegime::Ext => cont_largest = cont_largest.min(largest),
                }
                // The launchable set must be a PREFIX of the axis: occupancy falls
                // monotonically in the block size, so a hole would mean the query
                // is not measuring what this reads it as.
                assert_eq!(
                    launchable,
                    SEG_K
                        .into_iter()
                        .take_while(|&k| k <= largest)
                        .collect::<Vec<_>>(),
                    "{regime:?}/{coeff:?}/{epilogue:?}: the launchable set must be a prefix"
                );
            }
        }
    }
    let progptr = seg_launchable_k(
        BwdRegime::Ext,
        ProgramMode::DevPtr,
        CoeffMode::Constant,
        BwdSegEpilogue::Plane,
    );
    eprintln!("[seg-ladder] Ext/DevPtr-program launchable {progptr:?}");
    eprintln!(
        "[seg-ladder] largest LAUNCHABLE PROBED K over the axis {SEG_K:?}: R0 {r0_largest}, \
         continuation {cont_largest}; BWD_SEG_MAX_K {BWD_SEG_MAX_K}. 17..=31 is NOT probed — \
         Task 9's sweep must bisect it (start at 24) before concluding a ceiling."
    );

    assert_eq!(
        r0_largest, BWD_SEG_MAX_K,
        "the R0 family reached the geometry cap before; a drop means its register count grew"
    );
    // The CONTINUATION family reaches the geometry cap too, but for a different
    // reason than R0: its executor carries the folds and the dual-product pair
    // resolution, so it sits just under the 64 registers per thread a 1024-thread
    // block allows rather than comfortably below. That is a property of
    // `segmented_vm.cu`'s deliberate absence of `__launch_bounds__`, not of this
    // ladder, and it is pinned here so the number is a measurement on the record
    // rather than a launch failure someone rediscovers.
    assert_eq!(
        cont_largest, PINNED_CONT_LARGEST_LAUNCHABLE_PROBED_K,
        "the largest LAUNCHABLE PROBED continuation K moved (probed axis {SEG_K:?}; 17..=31 is \
         not probed, but the cap itself is: `BWD_SEG_MAX_K` is the geometry limit). Re-read the \
         register measurement before changing this pin, and widen `SEG_K` if it ROSE."
    );
    assert!(
        cont_largest >= 16,
        "a continuation value below 16 would leave the multi-warp epilogues barely covered"
    );
}

/// A small probe set inside one family's launchable axis: the shared-memory bypass
/// (`K = 1`), a middling multi-warp shape, and the family's OWN ceiling.
///
/// Used by the gates that vary something other than `K` and only need `K` to be
/// non-degenerate. Derived from the measurement rather than written down, so a gate
/// cannot ask for a block the kernel cannot host.
fn seg_probe_k(
    regime: BwdRegime,
    prog: ProgramMode,
    coeff: CoeffMode,
    epilogue: BwdSegEpilogue,
) -> Vec<usize> {
    let axis = seg_launchable_k(regime, prog, coeff, epilogue);
    let ceiling = *axis.last().expect("some K must be launchable");
    let mut probes: Vec<usize> = vec![1, 4, ceiling]
        .into_iter()
        .filter(|k| axis.contains(k))
        .collect();
    probes.sort_unstable();
    probes.dedup();
    probes
}

// ── The matrix ───────────────────────────────────────────────────────────────

/// Run one fixture over the `K` axis this family can launch, alternating the
/// coefficient loader so both specializations run at every `K` without doubling the
/// launch count, and assert every `K` produced BIT-IDENTICAL sums.
fn assert_k_axis(fixture: &mut SegFixture, eq: &StagedEq, context: &ProverContext) -> usize {
    // The INTERSECTION of the two coefficient loaders' axes: they are separate
    // kernels with separate register counts, and this loop alternates between them,
    // so a `K` only one of them can host would fail the launch rather than the
    // parity it is here to check.
    let devptr = seg_launchable_k(
        fixture.coord.regime,
        ProgramMode::Inline,
        CoeffMode::DevPtr,
        BwdSegEpilogue::Plane,
    );
    let axis: Vec<usize> = seg_launchable_k(
        fixture.coord.regime,
        ProgramMode::Inline,
        CoeffMode::Constant,
        BwdSegEpilogue::Plane,
    )
    .into_iter()
    .filter(|k| devptr.contains(k))
    .collect();
    let mut reference: Option<Vec<E4>> = None;
    for (index, k) in axis.iter().copied().enumerate() {
        let coeff = if index % 2 == 0 {
            CoeffMode::Constant
        } else {
            CoeffMode::DevPtr
        };
        let run = fixture.assert_shape(SegShape::inline(k, coeff), eq, context);
        match &reference {
            None => reference = Some(run.contributions),
            Some(first) => assert!(
                first
                    .iter()
                    .zip(&run.contributions)
                    .all(|(a, b)| e4_bits(*a) == e4_bits(*b)),
                "{}: K{k} diverged from K{} — segmentation must be invisible to the value",
                fixture.label(),
                axis[0]
            ),
        }
    }
    axis.len()
}

/// R0 over the whole corpus and the whole `K` axis.
///
/// R0 is the regime with no prologue, no seed and no fold: every window is at
/// target depth by definition, so this is the rung that isolates the DECODE loop
/// and the five R0 term classes — `C2ProductBfE4` in particular, where the wire's
/// BF-first operand order is an encoder invariant the kernel trusts rather than
/// checks.
#[test]
#[cfg(not(no_cuda))]
#[ignore = "GPU; build unlocked and run the executable under with_gpu_lock.sh"]
#[serial_test::serial]
fn bwd_seg_r0_parity_over_k_and_banks() {
    let context = make_seg_context();
    let eq = stage_eq(&context);
    let _claim = StagedClaimPoint;
    let mut launches = 0usize;
    let mut classes = BTreeSet::new();
    for circuit in SEG_LAYOUTS {
        let coord = lean_coordinate(circuit, 0, BwdRegime::R0);
        for record in decode_program(&coord.artifact.program).expect("decode") {
            classes.insert(record.class);
        }
        let mut fixture = SegFixture::build(coord, 0, SEG_ROWS, D2Policy::Inline, None, &context);
        launches += assert_k_axis(&mut fixture, &eq, &context);
    }
    // The corpus really reaches all five live R0 classes, so the launches above are
    // not a partial decode loop passing for a whole one.
    assert_eq!(
        classes,
        (0u8..5).collect(),
        "the R0 matrix must execute every live R0 term class"
    );
    eprintln!(
        "[seg-ladder] R0: {launches} launches over {} circuits, K axis {:?}",
        SEG_LAYOUTS.len(),
        seg_launchable_k(
            BwdRegime::R0,
            ProgramMode::Inline,
            CoeffMode::Constant,
            BwdSegEpilogue::Plane
        )
    );
    assert_eq!(
        launches,
        SEG_LAYOUTS.len() * SEG_K.len(),
        "R0 launches every K of the axis"
    );
}

/// The continuation regime at D0-D3, over the whole corpus and the whole `K` axis.
///
/// One artifact per `(circuit, Ext)` bound at four depths, which is what moves each
/// window's catch-up: D0 reads at target depth, D1 and D2 fold INLINE in the eval
/// loop, and D3 folds in the PROLOGUE and publishes. Every published window's
/// region is compared against the host fold as well, so the handshake is checked at
/// the depth that produces it.
#[test]
#[cfg(not(no_cuda))]
#[ignore = "GPU; build unlocked and run the executable under with_gpu_lock.sh"]
#[serial_test::serial]
fn bwd_seg_cont_d0_d3_parity_over_k() {
    let context = make_seg_context();
    let eq = stage_eq(&context);
    let _claim = StagedClaimPoint;
    let mut launches = 0usize;
    let mut published_rounds = BTreeSet::new();
    let mut classes: BTreeMap<u8, BTreeSet<u8>> = BTreeMap::new();
    for circuit in SEG_LAYOUTS {
        let coord = lean_coordinate(circuit, 0, BwdRegime::Ext);
        for round in 0u8..=3 {
            let mut fixture = SegFixture::build(
                Arc::clone(&coord),
                round,
                SEG_ROWS,
                D2Policy::Inline,
                None,
                &context,
            );
            if fixture.model.publishing().next().is_some() {
                published_rounds.insert(round);
            }
            classes
                .entry(round)
                .or_default()
                .extend(fixture.source_classes(&eq));
            launches += assert_k_axis(&mut fixture, &eq, &context);
        }
    }

    // The per-round SOURCE-CLASS census, over the union of the four circuits. This
    // is what turns "the matrix covers the fold paths" from a description of the
    // axes into a measurement of what the launches actually executed — an inline
    // depth-two fold that no circuit emitted would otherwise make the D2 rung
    // vacuous without anything saying so.
    eprintln!("[seg-ladder] source classes by round: {classes:?}");
    let seen = |round: u8, class: SourceClass| classes[&round].contains(&class.code());
    assert!(
        seen(0, SourceClass::BfDirect) && seen(0, SourceClass::ProceduralInline),
        "D0 must read raw base field and synthesize procedurally, both at depth zero"
    );
    assert!(
        seen(1, SourceClass::BfInlineD1) && seen(1, SourceClass::ProceduralInline),
        "D1 must fold raw base field and row synthesis INLINE, one step"
    );
    assert!(
        seen(2, SourceClass::BfInlineD2) && seen(2, SourceClass::ProceduralInline),
        "D2 under the Inline policy must fold raw base field and row synthesis INLINE, two steps"
    );
    // At the publication depth every raw origin has been materialized by the
    // prologue, so the eval loop sees ONE class. A surviving inline class here would
    // mean a source folding three steps in the eval loop, which the kernel's
    // `MAX_DEPTH` of two cannot do.
    assert_eq!(
        classes[&3],
        [SourceClass::E4Direct.code()].into_iter().collect(),
        "at D3 the prologue owns every fold, so every source must resolve as E4Direct"
    );
    // D3 publishes by construction (every DRAM source is three folds behind), so a
    // matrix in which nothing published would mean the prologue never ran.
    assert!(
        published_rounds.contains(&3),
        "no window published at D3: the JAOT prologue never ran"
    );
    let axis = seg_launchable_k(
        BwdRegime::Ext,
        ProgramMode::Inline,
        CoeffMode::Constant,
        BwdSegEpilogue::Plane,
    );
    eprintln!(
        "[seg-ladder] continuation: {launches} launches over K {axis:?}, rounds that published \
         {published_rounds:?}"
    );
    assert_eq!(launches, SEG_LAYOUTS.len() * 4 * axis.len());
}

/// Both D2 policies, on the same coordinate at the same round.
///
/// The one genuine policy choice in the assignment matrix: a base-field window two
/// folds behind is either folded INLINE in the eval loop (`BfInlineD2`, four raw
/// reads per endpoint, no DRAM write) or turned into a published E4 pyramid by the
/// prologue (`E4Direct` + `materialize`). The two produce the same value through
/// completely different kernel paths, which is why they are asserted BIT-IDENTICAL
/// to each other as well as to the oracle — the pyramid pairing was verified only
/// statically before this.
#[test]
#[cfg(not(no_cuda))]
#[ignore = "GPU; build unlocked and run the executable under with_gpu_lock.sh"]
#[serial_test::serial]
fn bwd_seg_d2_policies_agree() {
    let context = make_seg_context();
    let eq = stage_eq(&context);
    let _claim = StagedClaimPoint;
    let mut covered = false;
    for circuit in SEG_LAYOUTS {
        let coord = lean_coordinate(circuit, 0, BwdRegime::Ext);
        let mut by_policy = Vec::new();
        for d2 in [D2Policy::Inline, D2Policy::Materialize] {
            let mut fixture =
                SegFixture::build(Arc::clone(&coord), 2, SEG_ROWS, d2, None, &context);
            let classes = fixture.source_classes(&eq);
            match d2 {
                D2Policy::Inline => {
                    if classes.contains(&SourceClass::BfInlineD2.code()) {
                        covered = true;
                    }
                }
                D2Policy::Materialize => assert!(
                    !classes.contains(&SourceClass::BfInlineD2.code()),
                    "{}: Materialize must leave no inline depth-two source",
                    fixture.label()
                ),
            }
            let mut first: Option<Vec<E4>> = None;
            for k in seg_probe_k(
                BwdRegime::Ext,
                ProgramMode::Inline,
                CoeffMode::Constant,
                BwdSegEpilogue::Plane,
            ) {
                let run =
                    fixture.assert_shape(SegShape::inline(k, CoeffMode::Constant), &eq, &context);
                first.get_or_insert(run.contributions);
            }
            by_policy.push(first.expect("at least one K ran"));
        }
        let (inline, materialize) = (&by_policy[0], &by_policy[1]);
        assert!(
            inline
                .iter()
                .zip(materialize)
                .all(|(a, b)| e4_bits(*a) == e4_bits(*b)),
            "{}: the two D2 policies must agree bit for bit",
            short_name(circuit)
        );
    }
    assert!(
        covered,
        "no circuit produced a BfInlineD2 source at D2; the inline depth-two path is untested"
    );
}

/// All three epilogues, on one `(layer, K)` cell each and against one another.
///
/// The epilogues differ only in barrier count against shared-memory footprint, and
/// field addition is exact and associative, so they can only differ by a BUG. The
/// footprint is the reason this gate exists at all: `bwd_seg_epilogue_smem_bytes`
/// is mirrored by hand on the two sides of the ABI and nothing at build time
/// compares them, so a disagreement is an out-of-bounds shared access — silent
/// until a kernel actually runs with the wrong dynamic-smem argument.
///
/// Run at `K = 2` — where the staged epilogue's accumulate loop runs zero times —
/// and at the family's own [`PINNED_CONT_K_CEILING`], which is the widest plane the
/// continuation kernels can actually host. `K = 1` follows separately: all three
/// take the epilogue's early return there, and asserting that the early return is
/// also correct is what makes the `K = 1` column of the matrix mean something.
#[test]
#[cfg(not(no_cuda))]
#[ignore = "GPU; build unlocked and run the executable under with_gpu_lock.sh"]
#[serial_test::serial]
fn bwd_seg_epilogues_are_bit_identical() {
    let context = make_seg_context();
    let eq = stage_eq(&context);
    let _claim = StagedClaimPoint;
    let coord = lean_coordinate(ADD_SUB_LAYOUT, 0, BwdRegime::Ext);
    let mut fixture = SegFixture::build(coord, 3, SEG_ROWS, D2Policy::Inline, None, &context);
    // `K = 2` is where the staged epilogue's accumulate loop runs zero times; the
    // ceiling is the widest plane this family can actually host.
    let ceiling = [
        BwdSegEpilogue::Staged,
        BwdSegEpilogue::Plane,
        BwdSegEpilogue::Wide,
    ]
    .into_iter()
    .map(|epilogue| {
        *seg_launchable_k(
            BwdRegime::Ext,
            ProgramMode::Inline,
            CoeffMode::Constant,
            epilogue,
        )
        .last()
        .expect("some K must be launchable")
    })
    .min()
    .expect("three epilogues");
    for k in [2usize, ceiling] {
        let mut reference: Option<Vec<E4>> = None;
        for epilogue in [
            BwdSegEpilogue::Staged,
            BwdSegEpilogue::Plane,
            BwdSegEpilogue::Wide,
        ] {
            let bytes = bwd_seg_epilogue_smem_bytes(epilogue, k as u32);
            eprintln!("[seg-ladder] epilogue {epilogue:?} at K{k}: {bytes} B of dynamic smem");
            let shape = SegShape::inline(k, CoeffMode::Constant).with_epilogue(epilogue);
            let run = fixture.assert_shape(shape, &eq, &context);
            match &reference {
                None => reference = Some(run.contributions),
                Some(first) => assert!(
                    first
                        .iter()
                        .zip(&run.contributions)
                        .all(|(a, b)| e4_bits(*a) == e4_bits(*b)),
                    "{}: epilogue {epilogue:?} diverged at K{k}",
                    fixture.label()
                ),
            }
        }
    }
    // K == 1 takes the epilogue's early return in all three specializations: warp
    // 0's register partials ARE the block result, and no plane is touched.
    for epilogue in [
        BwdSegEpilogue::Staged,
        BwdSegEpilogue::Plane,
        BwdSegEpilogue::Wide,
    ] {
        assert_eq!(bwd_seg_epilogue_smem_bytes(epilogue, 1), 0);
        fixture.assert_shape(
            SegShape::inline(1, CoeffMode::Constant).with_epilogue(epilogue),
            &eq,
            &context,
        );
    }
}

/// A continuation layer with a NONZERO `acc_c0` seed, banked and reserved.
///
/// The `K` triangle passes vacuously at `c_init = 0`: a zero seed lands correctly
/// however many partials carry it. With a nonzero one, list 0 must carry it EXACTLY
/// ONCE — `K` seeded partials would reduce to `K * c_init` — so `K`-invariance on
/// this cell is what proves the seeding rule rather than assuming it. The seed also
/// travels as Montgomery LIMBS rather than a recipe index, so this is the only gate
/// that exercises the reinterpret.
///
/// Both id forms are covered because they resolve through different halves of one
/// payload: a reserved literal is materialized at the bank HEAD by lowering, a
/// banked recipe comes from the evaluated tail.
#[test]
#[cfg(not(no_cuda))]
#[ignore = "GPU; build unlocked and run the executable under with_gpu_lock.sh"]
#[serial_test::serial]
fn bwd_seg_nonzero_c_init_parity() {
    let context = make_seg_context();
    let eq = stage_eq(&context);
    let _claim = StagedClaimPoint;
    let coord = lean_coordinate(ADD_SUB_LAYOUT, 0, BwdRegime::Ext);
    assert!(
        !coord.layer.coefficients.is_empty(),
        "a banked c_init needs a bank"
    );
    // The corpus's own `c_init` at the tested coordinates, reported so a future
    // corpus that starts carrying one is noticed rather than shadowed by the
    // synthetic seeds below.
    let natural: Vec<String> = SEG_LAYOUTS
        .iter()
        .filter_map(|circuit| {
            let entry = lean_coordinate(circuit, 0, BwdRegime::Ext);
            entry
                .layer
                .c_init
                .map(|id| format!("{} -> {id:?}", short_name(circuit)))
        })
        .collect();
    eprintln!("[seg-ladder] corpus continuation layers with a natural c_init: {natural:?}");
    // The fixture set must contain a continuation layer that really carries a seed,
    // or every other cell of the matrix is running the zero-seed path and this gate
    // is the only thing standing between the ladder and a vacuous `K` triangle.
    assert!(
        !natural.is_empty(),
        "no corpus continuation layer carries a c_init; the rest of the matrix then only ever \
         runs the zero seed, so add a synthetic seeded fixture before trusting it"
    );

    // The two id forms resolve through different halves of ONE payload, so both are
    // covered: lowering materializes the reserved literals at the bank HEAD and the
    // evaluated recipes follow.
    let banked = CoefficientRecipeId::from_bank_index(0);
    let reserved = CoefficientRecipeId::ONE;
    assert!(banked.bank_index().is_some() && banked.literal().is_none());
    assert!(reserved.bank_index().is_none() && reserved.literal().is_some());
    for id in [banked, reserved] {
        let mut fixture = SegFixture::build(
            Arc::clone(&coord),
            2,
            SEG_ROWS,
            D2Policy::Inline,
            Some(id),
            &context,
        );
        // The seed the descriptor carries must be the payload entry the CPU oracle
        // resolves, and it must not be zero — otherwise this whole gate is the
        // vacuous one it exists to replace.
        let setup = fixture.lower_with(SegShape::inline(4, CoeffMode::Constant), &eq);
        let expected = setup.coefficients[id.0 as usize];
        assert_ne!(expected, E4::ZERO, "a zero seed proves nothing");
        assert_eq!(
            SegFixture::inline_desc(&setup).c_init,
            e4_limbs(expected),
            "the descriptor must carry the RESOLVED seed as in-memory limbs"
        );
        assert_k_axis(&mut fixture, &eq, &context);
    }
}

/// The device-program family: the stream uploaded to device memory and the
/// descriptor's pointer patched to it.
///
/// Only the continuation regime with the `const` coefficient loader is
/// instantiated, so that is the only cell; the point is that the SAME program read
/// from device memory instead of parameter space produces the same values.
#[test]
#[cfg(not(no_cuda))]
#[ignore = "GPU; build unlocked and run the executable under with_gpu_lock.sh"]
#[serial_test::serial]
fn bwd_seg_progptr_program_source_parity() {
    let context = make_seg_context();
    let eq = stage_eq(&context);
    let _claim = StagedClaimPoint;
    let coord = lean_coordinate(ADD_SUB_LAYOUT, 0, BwdRegime::Ext);
    let mut fixture = SegFixture::build(coord, 3, SEG_ROWS, D2Policy::Inline, None, &context);
    // The two program families are separate kernels with separate register counts,
    // so the probe set is the INTERSECTION of what both can host.
    let inline_axis = seg_probe_k(
        BwdRegime::Ext,
        ProgramMode::Inline,
        CoeffMode::Constant,
        BwdSegEpilogue::Plane,
    );
    let devptr_axis = seg_launchable_k(
        BwdRegime::Ext,
        ProgramMode::DevPtr,
        CoeffMode::Constant,
        BwdSegEpilogue::Plane,
    );
    let probes: Vec<usize> = inline_axis
        .into_iter()
        .filter(|k| devptr_axis.contains(k))
        .collect();
    // A filtered-to-empty axis is the vacuity this whole file is written against:
    // libtest is just as green for a gate that launched nothing as for one that
    // launched everything, so the intersection is asserted non-empty AND asserted to
    // contain the shape that matters (`K = 1` is the smem bypass; a set that had
    // collapsed to it alone would test no multi-warp device-program launch at all).
    assert!(
        probes.len() >= 2 && probes.contains(&1),
        "the device-program probe set collapsed to {probes:?}: inline and devptr occupancy must \
         overlap on more than one K, or this gate proves nothing"
    );
    let mut launched = 0usize;
    for k in probes.iter().copied() {
        let inline = fixture.assert_shape(SegShape::inline(k, CoeffMode::Constant), &eq, &context);
        let shape = SegShape {
            k,
            coeff: CoeffMode::Constant,
            prog: ProgramMode::DevPtr,
            epilogue: BwdSegEpilogue::Plane,
        };
        // Lowering leaves the pointer null and records the word count; `launch`
        // uploads the stream and patches the descriptor, which IS the mechanism for
        // a by-value parameter.
        let setup = fixture.lower_with(shape, &eq);
        match &setup.desc {
            BwdSegLaunchDesc::ProgPtr(desc) => {
                assert!(
                    desc.program.is_null(),
                    "lowering must leave the pointer null"
                );
                assert_eq!(desc.program_words as usize, setup.program_words.len());
                assert_eq!(
                    setup.program_words.len(),
                    usize::from(desc.list_offset[k]),
                    "the device stream is exactly the K-split stream"
                );
            }
            BwdSegLaunchDesc::Inline(_) => panic!("expected the device-program descriptor"),
        }
        let devptr = fixture.assert_shape(shape, &eq, &context);
        assert!(
            inline
                .contributions
                .iter()
                .zip(&devptr.contributions)
                .all(|(a, b)| e4_bits(*a) == e4_bits(*b)),
            "{}: the device-program family diverged from the inline one at K{k}",
            fixture.label()
        );
        launched += 1;
    }
    assert_eq!(
        launched,
        probes.len(),
        "every probed K must have run both program families"
    );
    eprintln!("[seg-ladder] device-program parity over K {probes:?}");
}

/// Row counts that are not whole tiles, including the shapes a deep round on a
/// small layer produces.
///
/// The last tile is partial and its dead lanes are CLAMPED onto the last live row
/// rather than returning, which is what keeps `__syncthreads()` block-uniform. A
/// clamped lane folds an in-bounds row, reduces into its own plane slot and stores
/// NOTHING — so the failure it guards against is a duplicate publish or a
/// double-counted partial, both of which this compares away.
#[test]
#[cfg(not(no_cuda))]
#[ignore = "GPU; build unlocked and run the executable under with_gpu_lock.sh"]
#[serial_test::serial]
fn bwd_seg_partial_tiles_clamp_dead_lanes() {
    let context = make_seg_context();
    let eq = stage_eq(&context);
    let _claim = StagedClaimPoint;
    let coord = lean_coordinate(ADD_SUB_LAYOUT, 0, BwdRegime::Ext);
    // 8 and 16 are a SINGLE partial tile (the shape a deep round on a small layer
    // gives); 40 is one whole tile plus a partial one; 64 is the whole-tile control,
    // so a bug that only appears without a clamp is still visible as a difference.
    for rows in [8usize, 16, 40, 64] {
        assert_eq!(
            rows % (WARP_SIZE as usize) == 0,
            rows == 64,
            "the row set must contain both partial and whole tiles"
        );
        let mut fixture = SegFixture::build(
            Arc::clone(&coord),
            3,
            rows,
            D2Policy::Inline,
            None,
            &context,
        );
        for k in seg_probe_k(
            BwdRegime::Ext,
            ProgramMode::Inline,
            CoeffMode::Constant,
            BwdSegEpilogue::Plane,
        ) {
            fixture.assert_shape(SegShape::inline(k, CoeffMode::Constant), &eq, &context);
        }
    }
}

/// The sequential d3 -> d4 chain, on ONE publish scratch: real ping-pong.
///
/// Round 3 folds every window three steps and publishes into parity 1; round 4
/// reads exactly those regions, folds one more step and publishes into parity 0.
/// Task 6's pointer-layout test proves the ALTERNATION; only this proves the native
/// prologue wrote and read the correct halves — round 4's oracle is built from
/// round 3's published values, so a prologue that stored the endpoint halves the
/// wrong way round produces a wrong round-4 contribution and nothing else changes.
///
/// The chain is asserted for a BF-origin window (the depth-three pyramid) and a
/// procedural one (row synthesis, no DRAM read at all), because those are the two
/// origins whose round-4 identity is E4 only BECAUSE round 3 materialized them.
#[test]
#[cfg(not(no_cuda))]
#[ignore = "GPU; build unlocked and run the executable under with_gpu_lock.sh"]
#[serial_test::serial]
fn bwd_seg_d3_to_d4_chain_ping_pongs() {
    let context = make_seg_context();
    let eq = stage_eq(&context);
    let _claim = StagedClaimPoint;

    // A coordinate carrying both origins the chain is about.
    let coord = SEG_LAYOUTS
        .iter()
        .map(|circuit| lean_coordinate(circuit, 0, BwdRegime::Ext))
        .find(|coord| {
            let windows = &coord.artifact.binding.windows;
            // BASE-FIELD, not merely non-procedural: the interesting half of the
            // chain is the depth-three BF pyramid, and an E4 window would satisfy
            // "not procedural" while folding an already-extension backing.
            // `backing_field()` answers `Base` for a virtual setup too, so the
            // procedural test has to be excluded explicitly.
            windows.iter().any(|window| window.is_procedural())
                && windows.iter().any(|window| {
                    !window.is_procedural() && window.backing_field() == FieldKind::Base
                })
        })
        .expect("the corpus must carry a layer with both a procedural window and a BASE-FIELD one");
    eprintln!(
        "[seg-ladder] chain coordinate: {}",
        short_name(coord.circuit)
    );

    // Both rounds land on a PARTIAL tile (80 = 2 tiles + 16, 40 = 1 tile + 8), so the
    // chain runs through the dead-lane clamp rather than around it.
    let rows_d3 = 80usize;
    let d3_model = seg_host_model(&coord, 3, rows_d3, D2Policy::Inline, E4Deltas::Publishing);
    assert!(
        d3_model.windows.iter().all(|window| window.publishes),
        "every window must publish at D3 for the chain to have a source"
    );
    let d4_model = seg_chained_model(&coord, &d3_model, 4, rows_d3 / 2);

    // ONE plan over BOTH rounds, so round 4's read offsets ARE round 3's write
    // offsets and the two parity buffers are the ping-pong pair. Planning from the
    // models is what makes this possible at all: round 4's read pointers come out of
    // the plan, so its lowered storage cannot also be an input to it.
    let scratch = Rc::new(SegScratch::new(&[&d3_model, &d4_model], &context));
    let d3_storage = upload_round_storage(&d3_model, &context);
    let d4_storage = chained_round_storage(&d4_model, &scratch.resolved());
    // Both origins really reach the prologue at D3: a base-field window (the
    // depth-three `8xBF -> E4` pyramid) and a procedural one (row synthesis, no DRAM
    // read at all). Read off the LOWERED windows rather than the families, since the
    // origin is a per-round statement.
    let d3_origins: BTreeSet<u8> = d3_storage
        .windows
        .iter()
        .zip(&d3_model.windows)
        .map(|(bound, host)| match (bound.read, host.publishes) {
            (None, _) => BWD_COEFF_ORIGIN_PROCEDURAL,
            (Some(column), _) if column.is_e4 => BWD_COEFF_ORIGIN_READ_EXT,
            (Some(_), _) => BWD_COEFF_ORIGIN_READ_BASE,
        })
        .collect();
    eprintln!("[seg-ladder] chain D3 window origins: {d3_origins:?}");
    assert!(
        d3_origins.contains(&BWD_COEFF_ORIGIN_READ_BASE),
        "the chain's D3 round must fold a BASE-FIELD window: that pyramid is the half the \
         d3->d4 handshake is really about"
    );
    assert!(
        d3_origins.contains(&BWD_COEFF_ORIGIN_PROCEDURAL),
        "the chain's D3 round must also synthesize a procedural window"
    );

    let mut d3 = SegFixture::finish(
        Arc::clone(&coord),
        d3_model,
        d3_storage,
        Rc::clone(&scratch),
        None,
        &context,
    );
    let mut d4 = SegFixture::finish(
        Arc::clone(&coord),
        d4_model,
        d4_storage,
        Rc::clone(&scratch),
        None,
        &context,
    );

    // The round's `procedural_kind` is a PER-ROUND statement, not the family's: a
    // virtual setup the previous round materialized resolves from DRAM now, and the
    // descriptor must say so or the kernel would re-synthesize it from the row.
    let setup = d4.lower_with(SegShape::inline(4, CoeffMode::Constant), &eq);
    let desc = SegFixture::inline_desc(&setup);
    let mut cleared = 0usize;
    for (index, bound) in coord.artifact.binding.windows.iter().enumerate() {
        assert_eq!(
            desc.window[index].origin, BWD_COEFF_ORIGIN_READ_EXT,
            "window {index} must read the previous round's E4 publication at D4"
        );
        if bound.is_procedural() {
            assert_eq!(
                desc.window[index].procedural_kind, BWD_COEFF_PROCEDURAL_NONE,
                "window {index} is a virtual setup, but at D4 it resolves from the scratch \
                 region and must not also look synthesizable"
            );
            cleared += 1;
        }
    }
    assert!(cleared > 0, "the chain must carry a procedural window");
    drop(setup);

    for k in seg_probe_k(
        BwdRegime::Ext,
        ProgramMode::Inline,
        CoeffMode::Constant,
        BwdSegEpilogue::Plane,
    ) {
        // Round 3 first, ALWAYS: round 4 reads what it published, so a run order
        // that reversed them would compare round 4 against a stale parity buffer.
        d3.assert_shape(SegShape::inline(k, CoeffMode::Constant), &eq, &context);
        d4.assert_shape(SegShape::inline(k, CoeffMode::Constant), &eq, &context);
    }
}

// ── The fold-weight bank ─────────────────────────────────────────────────────

/// The device truth tables against the host algebra, slot for slot.
///
/// The prelude kernel is the ONE producer of `ab_gkr_bwd_seg_fold_weights`, and the
/// flat fold reads that bank instead of walking the pyramid — so every fold value
/// the segmented VM will produce is downstream of these eleven slots. The host side
/// [`expected_fold_weights`] is pinned to the live pyramid's own recursion by
/// `seg_lower_tests`, which makes this the link that carries that proof onto the
/// device: nothing else compares the kernel's `q`-bit-to-challenge pairing, its
/// per-delta bases, or its `delta > round` zeroing against anything.
#[test]
#[cfg(not(no_cuda))]
#[ignore = "GPU; build unlocked and run the executable under with_gpu_lock.sh"]
#[serial_test::serial]
fn bwd_seg_fold_weight_bank_matches_the_truth_tables() {
    let context = make_seg_context();
    // The claim point is process-wide shared state; restore it like every other
    // test in this file that stages it.
    let _claim = StagedClaimPoint;
    // SAFETY: the pointer is the address of `ab_gkr_bwd_seg_fold_weights`, whose
    // declared extent is exactly BWD_SEG_FOLD_WEIGHT_SLOTS (mirrors the
    // CLAIM_POINT_SLOTS slab idiom above). One borrow per call site, each passed
    // straight into a single `memory_copy*` and dropped.
    let bank = || unsafe {
        DeviceSlice::from_raw_parts_mut(
            bwd_seg_fold_weights_device_ptr(),
            BWD_SEG_FOLD_WEIGHT_SLOTS,
        )
    };
    // 4 is the deepest legal case: CLAIM_POINT_SLOTS = 4 and `stage_claim_point`
    // asserts len <= slots, so round 5 would panic before the prelude ever ran.
    // Round 4 still exercises delta < round.
    for round in [1u8, 2, 3, 4] {
        // Re-poison EVERY case: a stale bank from the previous case must not be able
        // to satisfy this one. The sentinel is the suite's established poison value,
        // which is also what makes the `delta > round` zero-check non-vacuous — an
        // unwritten slot reads poison, not the zero the host expects.
        memory_copy(bank(), &[seg_publish_poison(0); BWD_SEG_FOLD_WEIGHT_SLOTS])
            .expect("weight bank poison");
        let claim_point = seg_claim_point(round);
        stage_claim_point(&claim_point, &context);
        launch_bwd_seg_build_fold_weights(u32::from(round), &context).expect("prelude launch");
        // `download_e4` takes a `DeviceAllocation`; the symbol slab is not one, so
        // this is its body applied to the slab directly.
        let mut readback = vec![E4::ZERO; BWD_SEG_FOLD_WEIGHT_SLOTS];
        memory_copy_async(&mut readback[..], bank(), context.get_exec_stream())
            .expect("weight bank D2H");
        context
            .get_exec_stream()
            .synchronize()
            .expect("weight bank sync");
        let expected = expected_fold_weights(u32::from(round), &claim_point);
        for slot in 0..BWD_SEG_FOLD_WEIGHT_SLOTS {
            assert_e4(
                &format!("weight slot {slot} mismatch at round {round}"),
                readback[slot],
                expected[slot],
            );
        }
    }
    // Leave the bank zeroed, mirroring the claim-point restore discipline.
    memory_copy(bank(), &[E4::ZERO; BWD_SEG_FOLD_WEIGHT_SLOTS]).expect("weight bank restore");
}
