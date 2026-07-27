//! Artifact-certified fixtures for the SEGMENTED lean VM's GPU parity ladder.
//!
//! The lean-artifact→[`BwdSegSetup`] bridge, and the HOST MODEL of the storage a
//! round reads. It is to [`seg_gpu_tests`](super::seg_gpu_tests) what
//! [`compile`](super::compile) was to [`gpu_tests`](super::gpu_tests), with one
//! structural difference that follows from the lineage: the cell-era bridge had to
//! pick a cell BUDGET and re-realize a paging plan per round, and a lean coordinate
//! has neither. What it has instead is a per-round PHYSICAL binding, so everything
//! here is about the round: which origin sits behind each window, how far behind
//! target depth it is, and what the fold of it must produce.
//!
//! # The three objects
//!
//! 1. [`lean_coordinate`] — one `(circuit, layer, regime)` compiled through
//!    `gkr_eval_isa`'s own `compile_lean_coordinate`, plus the semantic
//!    [`CoeffLayer`] the two CPU oracles run. Both come from the same
//!    `lower_lean_layer`, so they cannot describe different layers.
//! 2. [`SegHostModel`] — the synthetic storage: one [`SegHostWindow`] per bound
//!    window, its backing values, and the FOLD MODEL that turns them into the
//!    target-depth `(endpoint0, delta)` pair a source resolves to. This is the
//!    oracle's view of physical resolution, and it is deliberately written from
//!    `segmented_vm.cu`'s recurrence rather than from the incumbent's leaf form:
//!    see [`SegHostWindow::endpoints`].
//! 3. the device staging ([`upload_round_storage`], [`SegScratch`]) and the round
//!    binding ([`seg_round_binding`]) that [`lower_bwd_seg`] takes.
//!
//! # Why the origin is not a free choice
//!
//! `lower_bwd_seg` rejects a base-field or procedural backing at a nonzero depth
//! ([`BwdSegLowerError::BaseReadAtFoldedDepth`]) — a folded value is E4 by
//! construction. So a BF or procedural window's `backing_depth` is always ZERO and
//! its catch-up is therefore the ROUND itself, which is what makes round 1/2/3 the
//! D1/D2/D3 fold cases rather than a free `(origin, delta)` grid. Only an E4 window
//! has a real choice, and [`e4_deltas`] is that choice.
//!
//! # `--features bench`
//!
//! The whole module is behind the parent's `#[cfg(all(test, feature = "bench"))]`
//! gate, exactly like the cell-era bridge: a default `cargo test -p
//! gpu_circuit_prover` compiles none of it. See [`super`]'s module doc.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, OnceLock};

use cs::gkr_compiler::dag_ir::{
    bwd_roots, lower_dag, validate, BwdRegime, DagLayer, FieldKind, ReadPlace,
};
use era_cudart::memory::memory_copy_async;
use gkr_eval_isa::bwd::coeff::interp::CoeffResolver;
use gkr_eval_isa::bwd::coeff::lean_artifact::{
    compile_lean_coordinate, lower_lean_layer, LeanCoordinateArtifact,
};
use gkr_eval_isa::bwd::coeff::model::{CoeffLayer, CoefficientRecipeId, SourceId};
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use rayon::prelude::*;

use super::lower::ResolvedBwdCoeffSourceWindow;
use super::seg_lower::{
    assign_class, chain_read_column, plan_publish_scratch, window_columns, BwdSegRoundBinding,
    D2Policy, PublishScratchPlan, ResolvedPublishScratch, SourceOrigin,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::GkrEqSizes;
use crate::prover::gkr::forward::vm::lower::ResolvedColumn;
use crate::prover::ProverContext;
use crate::upstream::{Field, FieldExtension, PrimeField, TIMESTAMP_COLUMNS_NUM_BITS};

/// Bytes one element of a backing occupies, by storage field. Restated rather than
/// imported: `seg_lower`'s copies are private, and these are what the strides the
/// fixtures hand the descriptor are built from.
const BF_BYTES: usize = 4;
const E4_BYTES: usize = 16;

// ── The corpus the ladder runs ───────────────────────────────────────────────

/// The four committed layouts the parity matrix's circuit axis names.
///
/// `add_sub` is the ladder's reference coordinate (the cell-era ladder's too);
/// the other three are §15's focused set, chosen because they are the corpus
/// extremes in term count, source count and window mix.
pub(crate) const SEG_LAYOUTS: [&str; 4] = [
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
];

/// The ladder's reference coordinate.
pub(crate) const ADD_SUB_LAYOUT: &str = SEG_LAYOUTS[0];

/// A layout name shortened for assertion messages.
pub(crate) fn short_name(circuit: &str) -> &str {
    circuit
        .trim_end_matches(".json")
        .trim_end_matches("_layout_gkr")
}

type CrossFields = HashMap<ReadPlace, FieldKind>;

fn compiled_circuit_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits")
        .join(name)
}

/// One circuit's lowered DAG plus its whole-circuit cross-layer field map.
///
/// Cached because the largest layouts in [`SEG_LAYOUTS`] are tens of megabytes of
/// JSON and every fixture of every round needs the same lowering; the ladder walks
/// four circuits at up to five rounds, so this is the difference between four
/// parses and twenty.
fn lowered_dag(circuit: &'static str) -> Arc<(Vec<DagLayer>, CrossFields)> {
    static CACHE: OnceLock<Mutex<HashMap<&'static str, Arc<(Vec<DagLayer>, CrossFields)>>>> =
        OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(hit) = cache.lock().expect("dag cache").get(circuit) {
        return Arc::clone(hit);
    }
    let path = compiled_circuit_path(circuit);
    let bytes =
        std::fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let layout: crate::upstream::GKRCircuitArtifact<BF> = serde_json::from_slice(&bytes)
        .unwrap_or_else(|error| panic!("parse {}: {error}", path.display()));
    let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("[{circuit}] lower_dag: {error}"));
    validate(&dag).unwrap_or_else(|error| panic!("[{circuit}] validate: {error}"));
    let cross = build_cross_layer_field_map(&dag);
    let entry = Arc::new((dag.layers, cross));
    cache
        .lock()
        .expect("dag cache")
        .insert(circuit, Arc::clone(&entry));
    entry
}

/// One `(circuit, layer, regime)` lean coordinate: the artifact the GPU executes
/// and the semantic layer the CPU oracles interpret.
pub(crate) struct SegCoordinate {
    pub circuit: &'static str,
    pub layer_index: usize,
    pub regime: BwdRegime,
    /// The committed order, the fixed-width program and the placement-free source
    /// binding — everything `lower_bwd_seg` takes.
    pub artifact: LeanCoordinateArtifact,
    /// The semantic IR `interpret_coeff_layer` and `interpret_lean_program` run.
    pub layer: CoeffLayer,
}

impl SegCoordinate {
    /// This coordinate's addressable column count per bound window, straight from
    /// the artifact — the same function lowering derives it with, so a fixture and
    /// the descriptor cannot disagree about a window's span.
    pub fn columns(&self) -> Vec<usize> {
        window_columns(&self.artifact.binding).expect("a committed artifact binds legal windows")
    }
}

/// Compile one lean coordinate, cached.
///
/// Goes through `compile_lean_coordinate` rather than assembling
/// `lower → order → encode → bind` by hand: that function runs `validate_program`
/// and asserts the committed order is a permutation of the layer's terms, so a
/// program that reaches the GPU from here is well-formed and COMPLETE. The
/// semantic layer comes from `lower_lean_layer`, which is the same lowering
/// `compile_lean_coordinate` performs internally.
pub(crate) fn lean_coordinate(
    circuit: &'static str,
    layer_index: usize,
    regime: BwdRegime,
) -> Arc<SegCoordinate> {
    static CACHE: OnceLock<Mutex<HashMap<(&'static str, usize, bool), Arc<SegCoordinate>>>> =
        OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let key = (circuit, layer_index, regime == BwdRegime::R0);
    if let Some(hit) = cache.lock().expect("coordinate cache").get(&key) {
        return Arc::clone(hit);
    }
    let dag = lowered_dag(circuit);
    let canonical = dag
        .0
        .get(layer_index)
        .unwrap_or_else(|| panic!("{circuit} has no canonical layer {layer_index}"));
    assert!(
        !bwd_roots(canonical).is_empty(),
        "{circuit} L{layer_index} has no backward roots and is not a coordinate"
    );
    let label = format!("{} L{layer_index} {regime:?}", short_name(circuit));
    let (layer, _) = lower_lean_layer(canonical, &dag.1, regime)
        .unwrap_or_else(|error| panic!("lower {label}: {error:?}"));
    let artifact = compile_lean_coordinate(circuit, layer_index, canonical, &dag.1, regime)
        .unwrap_or_else(|error| panic!("compile {label}: {error:?}"));
    assert_eq!(
        artifact.binding.source_slots.len(),
        layer.sources.len(),
        "{label}: the binding must carry one slot per layer source"
    );
    let entry = Arc::new(SegCoordinate {
        circuit,
        layer_index,
        regime,
        artifact,
        layer,
    });
    cache
        .lock()
        .expect("coordinate cache")
        .insert(key, Arc::clone(&entry));
    entry
}

// ── Deterministic values ─────────────────────────────────────────────────────
//
// A compiled layer carries coefficient RECIPES, not values, and a round's fold
// challenges are transcript state. Every parity run therefore needs a
// deterministic stand-in for both, and the CPU oracles and the launch must use the
// SAME one — which is why they live here rather than in either test module.
//
// Four independent base digits per E4, so a BF/E4 width confusion cannot pass by
// coincidence.

fn fnv(mut acc: u32, words: &[u32]) -> u32 {
    for word in words {
        for byte in word.to_le_bytes() {
            acc ^= u32::from(byte);
            acc = acc.wrapping_mul(16_777_619);
        }
    }
    acc
}

pub(crate) fn seg_digit(tag: u32, a: u32, b: u32) -> BF {
    BF::from_u32_with_reduction(fnv(2_166_136_261, &[tag, a, b]))
}

pub(crate) fn seg_ext(tag: u32, a: u32, b: u32) -> E4 {
    E4::from_array_of_base([
        seg_digit(tag, a, b),
        seg_digit(tag ^ 0x11, a, b),
        seg_digit(tag ^ 0x22, a, b),
        seg_digit(tag ^ 0x33, a, b),
    ])
}

/// The fold challenge drawn at round `index`.
///
/// A pure function of the ROUND, not of the launch: the claim point is
/// front-indexed (slot `d` is round `d`'s challenge), so two consecutive rounds of
/// one chain must agree on every slot they share. A per-launch value would make the
/// d3→d4 chain unverifiable.
pub(crate) fn seg_challenge(index: usize) -> E4 {
    seg_ext(0x0d00, index as u32, 0)
}

/// The claim point one round needs: slots `0..round`, which is exactly the span the
/// deepest catch-up at `round` reads.
pub(crate) fn seg_claim_point(round: u8) -> Vec<E4> {
    (0..usize::from(round)).map(seg_challenge).collect()
}

/// The evaluated coefficient bank for one `(layer, round)`, RESERVED-EXCLUSIVE —
/// which is what [`BwdSegRoundBinding::coefficients`] wants; lowering materializes
/// `ONE` and `NEG_ONE` at the payload head itself.
///
/// Round-dependent on purpose: a recipe's VALUE is evaluated in the round's
/// challenge context, so a launch that reused the previous round's uploaded bank
/// would be caught by the d3→d4 chain instead of passing.
pub(crate) fn seg_bank(layer: &CoeffLayer, round: u8) -> Vec<E4> {
    (0..layer.coefficients.len())
        .map(|index| seg_ext(0xc0ef, index as u32, u32::from(round)))
        .collect()
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

fn lift(value: BF) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(value)
}

// ── The host storage model ───────────────────────────────────────────────────

/// What sits behind one synthetic window.
#[derive(Clone, Debug)]
pub(crate) enum SegBacking {
    /// Column-major base field: `values[column * column_len + index]`.
    Bf(Vec<BF>),
    /// Column-major extension field.
    Ext(Vec<E4>),
    /// A virtual setup, produced from the backing INDEX rather than read. Single
    /// column by construction, so there is no column term in its addressing —
    /// exactly as `seg_raw_synthesized` ignores `record.column`.
    Procedural(u8),
}

/// One synthetic source window at ONE round.
#[derive(Clone, Debug)]
pub(crate) struct SegHostWindow {
    pub index: usize,
    pub backing_depth: u8,
    /// Always the round: `lower_bwd_seg` requires it
    /// (`WindowTargetDepthMismatch`).
    pub target_depth: u8,
    /// Whether the prologue publishes for this window this round — the second half
    /// of [`assign_class`]'s answer, kept here so the plan, the descriptor and the
    /// oracle all read ONE decision.
    pub publishes: bool,
    /// Elements per column, in the backing's own width: `2 * rows << delta`.
    pub column_len: usize,
    pub backing: SegBacking,
}

/// `prod_k (leaf_k ? ch[backing + k] : 1 - ch[backing + k])`.
fn fold_weight(leaf: usize, delta: u8, backing_depth: u8, challenges: &[E4]) -> E4 {
    let mut weight = E4::ONE;
    for k in 0..usize::from(delta) {
        let challenge = challenges[usize::from(backing_depth) + k];
        let factor = if (leaf >> k) & 1 == 1 {
            challenge
        } else {
            let mut one_minus = E4::ONE;
            one_minus.sub_assign(&challenge);
            one_minus
        };
        weight.mul_assign(&factor);
    }
    weight
}

/// Leaf bit `k` weights `challenges[backing_depth + k]` and pyramid level `k + 1`
/// combines two values `span << (delta - 1 - k)` apart, so the leaf's backing
/// offset is its bit-reversed value times the target-depth span.
fn bit_reverse(leaf: usize, width: u8) -> usize {
    let width = usize::from(width);
    (0..width).fold(0, |acc, k| acc | (((leaf >> k) & 1) << (width - 1 - k)))
}

impl SegHostWindow {
    pub fn delta(&self) -> u8 {
        self.target_depth - self.backing_depth
    }

    /// One raw backing element, lifted into E4.
    fn element(&self, column: usize, index: usize) -> E4 {
        match &self.backing {
            SegBacking::Bf(values) => lift(values[column * self.column_len + index]),
            SegBacking::Ext(values) => values[column * self.column_len + index],
            SegBacking::Procedural(kind) => lift(procedural_value(*kind, index)),
        }
    }

    /// The target-depth `(endpoint0, endpoint1)` pair of `column` at `row`.
    ///
    /// The pyramid `segmented_vm.cu`'s `seg_fold_level` evaluates, written as its
    /// leaf sum: level `L` of a `delta`-step pyramid weights with
    /// `claim_point[backing_depth + L - 1]` and combines two values
    /// `span << (delta - L)` apart, so leaf bit `k` (level `k + 1`) carries
    /// challenge `backing_depth + k` and offset `span << (delta - 1 - k)` — which
    /// is the bit-reversal below. THE STRIDE RUNS OPPOSITE TO THE CHALLENGE INDEX:
    /// pairing the latest challenge with the widest stride folds correctly at
    /// delta 1 and silently transposes the challenges at delta 2 and 3, so this is
    /// the one place the ladder must not paraphrase the kernel.
    ///
    /// A publishing window resolves through the SAME expression: the prologue
    /// computes this fold and stores it, and eval reads the store back, so there is
    /// no second oracle for the published path — only [`SegHostModel::published`],
    /// which asserts the bytes really landed.
    pub fn endpoints(&self, column: usize, row: usize, rows: usize, challenges: &[E4]) -> (E4, E4) {
        let delta = self.delta();
        if delta == 0 {
            return (self.element(column, row), self.element(column, rows + row));
        }
        let span = 2 * rows;
        let mut s0 = E4::ZERO;
        let mut s1 = E4::ZERO;
        for leaf in 0..(1usize << delta) {
            let weight = fold_weight(leaf, delta, self.backing_depth, challenges);
            let offset = bit_reverse(leaf, delta) * span;
            let mut low = self.element(column, row + offset);
            low.mul_assign(&weight);
            s0.add_assign(&low);
            let mut high = self.element(column, rows + row + offset);
            high.mul_assign(&weight);
            s1.add_assign(&high);
        }
        (s0, s1)
    }
}

/// The whole synthetic storage of one `(coordinate, round, rows)` cell.
pub(crate) struct SegHostModel {
    pub circuit: &'static str,
    pub layer_index: usize,
    pub regime: BwdRegime,
    pub round: u8,
    pub rows: usize,
    pub d2: D2Policy,
    pub windows: Vec<SegHostWindow>,
    /// Per source slot, in slot order: `(window, window-relative column)`.
    pub slots: Vec<(usize, usize)>,
    /// Addressable columns per window, from the artifact.
    pub columns: Vec<usize>,
    /// Claim-point slots `0..round`.
    pub challenges: Vec<E4>,
    /// The evaluated bank, reserved-EXCLUSIVE.
    pub bank: Vec<E4>,
}

/// The E4 catch-up distances a round admits.
///
/// Zero and one are always legal; the third is the round's own fold depth, which
/// is the only other distance the pyramid is instantiated for
/// (`BwdSegLowerError::UnsupportedFoldDelta`). Rounds past the publication depth
/// have fold depth one, so their set is `{0, 1}` — which is the steady state.
pub(crate) fn e4_deltas(round: u8) -> Vec<u8> {
    let fold_depth = super::bwd_coeff_fold_depth(round);
    let mut out = vec![0u8];
    if fold_depth >= 1 {
        out.push(1);
    }
    if fold_depth > 1 {
        out.push(fold_depth);
    }
    out.retain(|delta| *delta <= round);
    out
}

/// Which of the supported E4 catch-up distances a fixture draws from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum E4Deltas {
    /// The whole supported set, ZERO included — so one round's matrix contains both
    /// a window read at target depth and windows that chain. The default.
    Supported,
    /// Only the NONZERO distances, i.e. every E4 window publishes.
    ///
    /// What the d3→d4 chain needs, and it is a hard requirement rather than a
    /// preference: at round `r + 1` a base-field or procedural window would need
    /// catch-up `r + 1`, which no fold depth past the publication threshold serves
    /// (`UnsupportedFoldDelta`), and an E4 window that did NOT publish at round `r`
    /// has nothing in the scratch to chain from. So the chain exists only if round
    /// `r` materialized every window.
    Publishing,
}

/// Build the host storage for one `(coordinate, round, rows, D2 policy)` cell.
///
/// The window FAMILIES, their column spans and the source→`(window, column)` map
/// are the COMPILER's; only the backing values and each E4 window's catch-up
/// distance are the fixture's, because a compiled artifact carries no device
/// address and no round.
pub(crate) fn seg_host_model(
    coord: &SegCoordinate,
    round: u8,
    rows: usize,
    d2: D2Policy,
    e4: E4Deltas,
) -> SegHostModel {
    assert!(rows > 0, "a launch with no rows evaluates nothing");
    let columns = coord.columns();
    let mut deltas = e4_deltas(round);
    if e4 == E4Deltas::Publishing {
        deltas.retain(|delta| *delta > 0);
        assert!(
            !deltas.is_empty(),
            "round {round} has no nonzero catch-up, so no E4 window can publish there"
        );
    }
    let mut windows = Vec::with_capacity(columns.len());
    for (index, bound) in coord.artifact.binding.windows.iter().enumerate() {
        let count = columns[index];
        // A base-field or procedural backing is NEVER at a nonzero depth: a value
        // at depth `k > 0` is the output of `k` E4-weighted folds, so only an E4
        // backing can honestly carry one (`BaseReadAtFoldedDepth`). Their catch-up
        // is therefore the round itself, and that is what makes rounds 1/2/3 the
        // D1/D2/D3 fold cases.
        let (origin, delta) = match (bound.procedural_kind(), bound.backing_field()) {
            (Some(_), _) => (SourceOrigin::Procedural, round),
            (None, FieldKind::Base) => (SourceOrigin::Bf, round),
            (None, FieldKind::Ext) => (SourceOrigin::E4, deltas[index % deltas.len()]),
        };
        let column_len = (2 * rows) << usize::from(delta);
        // Widely separated seeds, so a window that read another window's backing
        // produces visibly wrong values rather than plausible ones.
        let seed = 0x0100_0000u32 + ((index as u32) << 20);
        let backing = match origin {
            SourceOrigin::Procedural => {
                SegBacking::Procedural(bound.procedural_kind().expect("a procedural family"))
            }
            SourceOrigin::Bf => SegBacking::Bf(
                (0..count * column_len)
                    .map(|slot| seg_digit(seed, slot as u32, u32::from(round)))
                    .collect(),
            ),
            SourceOrigin::E4 => SegBacking::Ext(
                (0..count * column_len)
                    .map(|slot| seg_ext(seed, slot as u32, u32::from(round)))
                    .collect(),
            ),
        };
        let (_, publishes) = assign_class(origin, delta, d2);
        windows.push(SegHostWindow {
            index,
            backing_depth: round - delta,
            target_depth: round,
            publishes,
            column_len,
            backing,
        });
    }
    finish_model(coord, round, rows, d2, windows, columns)
}

/// Build the host storage for the round that CHAINS off `previous`.
///
/// Every window resolves from the region the previous round published: origin E4,
/// backing depth the previous round, catch-up one, and publishing again — which is
/// the real ping-pong the d3→d4 gate is about. The previous round's published
/// values ARE this round's backing, so a prologue that wrote or read the wrong
/// parity half cannot agree with this model.
pub(crate) fn seg_chained_model(
    coord: &SegCoordinate,
    previous: &SegHostModel,
    round: u8,
    rows: usize,
) -> SegHostModel {
    assert_eq!(
        usize::from(round),
        usize::from(previous.round) + 1,
        "a chain step is one round"
    );
    assert_eq!(rows * 2, previous.rows, "the row count halves per round");
    let columns = coord.columns();
    let mut windows = Vec::with_capacity(columns.len());
    for (index, count) in columns.iter().copied().enumerate() {
        let source = &previous.windows[index];
        assert!(
            source.publishes,
            "window {index} did not publish at round {}, so round {round} has nothing to chain \
             from",
            previous.round
        );
        let mut values = Vec::with_capacity(count * 2 * previous.rows);
        for column in 0..count {
            values.extend(previous.published(index, column));
        }
        windows.push(SegHostWindow {
            index,
            backing_depth: previous.round,
            target_depth: round,
            // An E4 window one fold behind publishes: that is the chain step.
            publishes: true,
            column_len: 2 * previous.rows,
            backing: SegBacking::Ext(values),
        });
    }
    finish_model(coord, round, rows, previous.d2, windows, columns)
}

fn finish_model(
    coord: &SegCoordinate,
    round: u8,
    rows: usize,
    d2: D2Policy,
    windows: Vec<SegHostWindow>,
    columns: Vec<usize>,
) -> SegHostModel {
    let slots = coord
        .artifact
        .binding
        .source_slots
        .iter()
        .map(|slot| (usize::from(slot.window), usize::from(slot.column)))
        .collect::<Vec<_>>();
    for (source, &(window, column)) in slots.iter().enumerate() {
        assert!(
            window < windows.len() && column < columns[window],
            "{}: source {source} names ({window}, {column}) outside the binding",
            short_name(coord.circuit)
        );
    }
    SegHostModel {
        circuit: coord.circuit,
        layer_index: coord.layer_index,
        regime: coord.regime,
        round,
        rows,
        d2,
        windows,
        slots,
        columns,
        challenges: seg_claim_point(round),
        bank: seg_bank(&coord.layer, round),
    }
}

impl SegHostModel {
    /// Every source's `(endpoint0, delta)` pair at every row, source-major.
    ///
    /// Precomputed rather than resolved per operand: the two CPU oracles between
    /// them resolve each source once per TERM, and a deep pyramid costs sixteen
    /// leaf reads, so a table turns the oracle from the ladder's dominant cost into
    /// noise. It is also the only form in which the fold is computed exactly once
    /// per `(source, row)`, which is what the kernel does.
    pub fn pair_table(&self) -> Vec<(E4, E4)> {
        let rows = self.rows;
        let windows = &self.windows;
        let challenges = &self.challenges;
        self.slots
            .par_iter()
            .flat_map_iter(move |&(window, column)| {
                (0..rows).map(move |row| {
                    let (s0, s1) = windows[window].endpoints(column, row, rows, challenges);
                    let mut delta = s1;
                    delta.sub_assign(&s0);
                    (s0, delta)
                })
            })
            .collect()
    }

    /// What the prologue must have written for one publishing `(window, column)`:
    /// `2 * rows` E4 values, endpoint 0 in `[0, rows)` and endpoint 1 in
    /// `[rows, 2 * rows)` — the split-halves layout every read, fold and publish in
    /// this lineage inherits.
    pub fn published(&self, window: usize, column: usize) -> Vec<E4> {
        let host = &self.windows[window];
        let mut out = Vec::with_capacity(2 * self.rows);
        let mut high = Vec::with_capacity(self.rows);
        for row in 0..self.rows {
            let (s0, s1) = host.endpoints(column, row, self.rows, &self.challenges);
            out.push(s0);
            high.push(s1);
        }
        out.extend(high);
        out
    }

    /// The label every assertion of this cell carries.
    pub fn label(&self) -> String {
        format!(
            "{} L{} {:?} r{} rows{} {:?}",
            short_name(self.circuit),
            self.layer_index,
            self.regime,
            self.round,
            self.rows,
            self.d2
        )
    }

    /// Windows this round's prologue publishes for.
    pub fn publishing(&self) -> impl Iterator<Item = &SegHostWindow> {
        self.windows.iter().filter(|window| window.publishes)
    }
}

/// The [`CoeffResolver`] both CPU oracles resolve through: a table lookup plus the
/// evaluated bank.
pub(crate) struct SegResolver<'a> {
    pub table: &'a [(E4, E4)],
    pub rows: usize,
    pub bank: &'a [E4],
}

impl CoeffResolver for SegResolver<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> E4 {
        let slot = id
            .bank_index()
            .expect("a reserved literal never reaches the bank");
        self.bank[slot]
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (E4, E4) {
        self.table[id.0 as usize * self.rows + row]
    }
}

// ── Device staging ───────────────────────────────────────────────────────────

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

pub(crate) fn download_e4(
    device: &DeviceAllocation<E4>,
    len: usize,
    context: &ProverContext,
) -> Vec<E4> {
    let mut host = vec![E4::ZERO; len];
    memory_copy_async(&mut host[..], &device[..len], context.get_exec_stream())
        .expect("synthetic E4 D2H");
    context
        .get_exec_stream()
        .synchronize()
        .expect("synthetic stream sync");
    host
}

/// Every backing one round uploaded, kept alive for the whole launch AND for the
/// downloads that synchronize the stream after it. Two typed vectors rather than a
/// tagged enum: a variant held purely for RAII has a field nothing reads.
#[derive(Default)]
pub(crate) struct SegBackings {
    bf: Vec<DeviceAllocation<BF>>,
    ext: Vec<DeviceAllocation<E4>>,
}

/// One round's device geometry: the uploaded backings plus the per-window round
/// binding `lower_bwd_seg` takes.
pub(crate) struct SegRoundStorage {
    /// Held for RAII only; the descriptor carries raw pointers into it.
    _backings: SegBackings,
    pub windows: Vec<ResolvedBwdCoeffSourceWindow>,
    pub read_elements: Vec<u32>,
}

/// Upload one round's raw backings.
pub(crate) fn upload_round_storage(
    model: &SegHostModel,
    context: &ProverContext,
) -> SegRoundStorage {
    let mut backings = SegBackings::default();
    let mut windows = Vec::with_capacity(model.windows.len());
    let mut read_elements = Vec::with_capacity(model.windows.len());
    for host in &model.windows {
        let read = match &host.backing {
            SegBacking::Bf(values) => {
                let device = upload(values, context);
                let column = ResolvedColumn {
                    is_e4: false,
                    ptr: device.as_ptr().cast(),
                    matrix_base: device.as_ptr() as *mut u8,
                    stride_bytes: (host.column_len * BF_BYTES) as u32,
                };
                backings.bf.push(device);
                Some(column)
            }
            SegBacking::Ext(values) => {
                let device = upload(values, context);
                let column = ResolvedColumn {
                    is_e4: true,
                    ptr: device.as_ptr().cast(),
                    matrix_base: device.as_ptr() as *mut u8,
                    stride_bytes: (host.column_len * E4_BYTES) as u32,
                };
                backings.ext.push(device);
                Some(column)
            }
            // No matrix at all: the resolver synthesizes from the row index.
            SegBacking::Procedural(_) => None,
        };
        read_elements.push(if read.is_some() {
            host.column_len as u32
        } else {
            0
        });
        windows.push(ResolvedBwdCoeffSourceWindow {
            read,
            // Publish geometry is the scratch plan's, never the caller's:
            // `lower_bwd_seg` rejects a caller-supplied one outright
            // (`UnexpectedPublishBacking`).
            publish: None,
            backing_depth: host.backing_depth,
            target_depth: host.target_depth,
            materialize: host.publishes,
        });
    }
    SegRoundStorage {
        _backings: backings,
        windows,
        read_elements,
    }
}

/// Bind one round's windows to the region the PREVIOUS round published, through
/// [`chain_read_column`] — the one place the parity-plus-offset arithmetic lives.
/// `lower_bwd_seg` re-derives the same address and rejects a disagreement
/// (`ChainReadNotPriorPublish`), so this cannot silently point elsewhere.
pub(crate) fn chained_round_storage(
    model: &SegHostModel,
    scratch: &ResolvedPublishScratch,
) -> SegRoundStorage {
    let mut windows = Vec::with_capacity(model.windows.len());
    let mut read_elements = Vec::with_capacity(model.windows.len());
    for host in &model.windows {
        let (ptr, stride_bytes) = chain_read_column(scratch, u32::from(model.round), host.index)
            .unwrap_or_else(|| {
                panic!(
                    "round {} published nothing for window {}",
                    model.round - 1,
                    host.index
                )
            });
        assert_eq!(
            stride_bytes as usize,
            host.column_len * E4_BYTES,
            "the chain read stride must be the previous round's publish stride"
        );
        read_elements.push(host.column_len as u32);
        windows.push(ResolvedBwdCoeffSourceWindow {
            read: Some(ResolvedColumn {
                is_e4: true,
                ptr,
                matrix_base: ptr as *mut u8,
                stride_bytes,
            }),
            publish: None,
            backing_depth: host.backing_depth,
            target_depth: host.target_depth,
            materialize: host.publishes,
        });
    }
    SegRoundStorage {
        _backings: SegBackings::default(),
        windows,
        read_elements,
    }
}

/// The publish scratch: a plan over a whole round sequence plus the two parity
/// buffers.
///
/// Allocated as `E4` rather than `u8` so the base of every publish region is
/// 16-byte aligned, which the prologue's `e4` stores require. Each parity buffer is
/// its own allocation, so the disjointness `check_alias` demands holds by
/// construction rather than by arithmetic.
pub(crate) struct SegScratch {
    pub plan: PublishScratchPlan,
    parity: [Option<DeviceAllocation<E4>>; 2],
}

impl SegScratch {
    /// Plan and allocate the sequence whose only populated rounds are `models`,
    /// ascending and ending at the deepest one.
    ///
    /// Built from the MODELS rather than from a lowered storage: the planner reads
    /// only each window's `materialize` declaration and each window's column count,
    /// and both are the model's ([`SegHostWindow::publishes`] is the second half of
    /// [`assign_class`]'s answer). That is also what breaks the circularity of the
    /// chain case — round `r + 1`'s read pointers come FROM the plan, so its storage
    /// cannot be an input to planning it.
    ///
    /// The unpopulated earlier rounds are present but EMPTY, which is legitimate (a
    /// round that planned nothing) and is what makes `chain_read_column` answer
    /// `None` for every window of a single-round fixture — so its raw reads cannot
    /// trip `RawReadOverPriorPublish`.
    pub fn new(models: &[&SegHostModel], context: &ProverContext) -> Self {
        assert!(!models.is_empty(), "a plan needs at least one round");
        assert!(
            models.windows(2).all(|pair| pair[0].round < pair[1].round),
            "the planned rounds must ascend"
        );
        let last = usize::from(models[models.len() - 1].round);
        let deepest_rows = models[models.len() - 1].rows;

        // One declaration-only window per model window: `materialize` is the only
        // field `plan_publish_scratch` reads.
        let declared: Vec<Vec<ResolvedBwdCoeffSourceWindow>> = models
            .iter()
            .map(|model| {
                model
                    .windows
                    .iter()
                    .map(|window| ResolvedBwdCoeffSourceWindow {
                        read: None,
                        publish: None,
                        backing_depth: window.backing_depth,
                        target_depth: window.target_depth,
                        materialize: window.publishes,
                    })
                    .collect()
            })
            .collect();

        let empty_windows: Vec<ResolvedBwdCoeffSourceWindow> = Vec::new();
        let empty_columns: Vec<usize> = Vec::new();
        let mut window_sets: Vec<&[ResolvedBwdCoeffSourceWindow]> = Vec::new();
        let mut column_sets: Vec<&[usize]> = Vec::new();
        let mut rows_per_round: Vec<usize> = Vec::new();
        for round in 0..=last {
            match models
                .iter()
                .position(|model| usize::from(model.round) == round)
            {
                Some(index) => {
                    window_sets.push(&declared[index]);
                    column_sets.push(&models[index].columns);
                    rows_per_round.push(models[index].rows);
                }
                None => {
                    window_sets.push(&empty_windows);
                    column_sets.push(&empty_columns);
                    // Halving per round, indexed by ABSOLUTE round.
                    rows_per_round.push(deepest_rows << (last - round));
                }
            }
        }
        let plan = plan_publish_scratch(&window_sets, &column_sets, &rows_per_round)
            .unwrap_or_else(|error| {
                panic!("{}: plan: {error:?}", models[models.len() - 1].label())
            });
        Self::allocate(plan, context)
    }

    fn allocate(plan: PublishScratchPlan, context: &ProverContext) -> Self {
        let parity = [0usize, 1].map(|index| {
            let bytes = plan.bytes_per_parity[index];
            (bytes > 0).then(|| {
                assert_eq!(bytes % E4_BYTES, 0, "a publish region is a whole e4 count");
                // Poisoned rather than zeroed: an unwritten publish slot the eval
                // loop then reads must produce a visibly wrong contribution, not a
                // plausible zero.
                let poison = vec![seg_ext(0xdead, index as u32, 0); bytes / E4_BYTES];
                upload(&poison, context)
            })
        });
        Self { plan, parity }
    }

    pub fn resolved(&self) -> ResolvedPublishScratch {
        ResolvedPublishScratch {
            parity_base: [0usize, 1].map(|index| match &self.parity[index] {
                Some(device) => device.as_ptr() as *mut u8,
                None => std::ptr::null_mut(),
            }),
            plan: self.plan.clone(),
        }
    }

    /// The whole parity buffer round `round` writes into, as E4 values.
    ///
    /// Downloaded whole rather than region by region: a corpus window can address
    /// 128 columns, and one D2H plus host-side offset arithmetic is the difference
    /// between one synchronization per launch and a thousand.
    pub fn download_write_parity(&self, round: u8, context: &ProverContext) -> Vec<E4> {
        let parity = usize::from(round & 1);
        match &self.parity[parity] {
            None => Vec::new(),
            Some(device) => {
                let len = self.plan.bytes_per_parity[parity] / E4_BYTES;
                download_e4(device, len, context)
            }
        }
    }

    /// Where one `(round, window, column)` publish region starts inside its parity
    /// buffer, in E4 values, or `None` for a window that publishes nothing there.
    ///
    /// The SAME `base + column * stride` arithmetic `lower_window` gives the
    /// descriptor, so a region this names and a region the prologue writes are the
    /// same bytes by construction.
    pub fn region_offset(&self, round: u8, window: usize, column: usize) -> Option<usize> {
        let layout = self.plan.per_round.get(usize::from(round))?;
        let offset = *layout.window_base.get(window)?;
        (offset != super::seg_lower::PUBLISH_WINDOW_ABSENT)
            .then(|| (offset + column * layout.column_stride_bytes) / E4_BYTES)
    }
}

/// Assemble one round's [`BwdSegRoundBinding`].
///
/// Every physical quantity comes from exactly one place: the windows and read
/// spans from [`SegRoundStorage`], the challenges and coefficients from the host
/// model, and the runtime pointers from the caller — so there is no second copy of
/// any of them to disagree with the descriptor.
#[allow(clippy::too_many_arguments)]
pub(crate) fn seg_round_binding<'a>(
    model: &'a SegHostModel,
    storage: &'a SegRoundStorage,
    claim_point: &'a [E4],
    coefficients: &'a [E4],
    c_init: Option<CoefficientRecipeId>,
    eq_low: *const E4,
    eq_sizes: GkrEqSizes,
    contributions: *mut E4,
) -> BwdSegRoundBinding<'a> {
    BwdSegRoundBinding {
        round: u32::from(model.round),
        rows: model.rows,
        windows: &storage.windows,
        window_read_elements: &storage.read_elements,
        claim_point,
        coefficients,
        c_init,
        eq_low,
        eq_sizes,
        contributions,
        acc_size: model.rows as u32,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gkr_eval_isa::bwd::coeff::limits::TermCategory;

    /// The fold model is the kernel's recurrence, not a paraphrase of it: at
    /// delta 1 it must be `f0 + r * (f1 - f0)` over the two values one target-depth
    /// span apart, and at delta 2 it must be that recurrence applied twice with the
    /// LATER challenge on the NARROWER stride.
    ///
    /// This is the pairing `segmented_vm.cu` calls out as the silent-transposition
    /// hazard, so it is pinned here directly rather than only through a GPU run.
    #[test]
    fn the_fold_model_is_the_kernel_recurrence() {
        let rows = 3usize;
        let span = 2 * rows;
        let challenges = seg_claim_point(2);
        let values: Vec<E4> = (0..4 * span)
            .map(|slot| seg_ext(0x77, slot as u32, 0))
            .collect();
        let fold = |f0: E4, f1: E4, challenge: E4| {
            let mut out = f1;
            out.sub_assign(&f0);
            out.mul_assign(&challenge);
            out.add_assign(&f0);
            out
        };

        let one_step = SegHostWindow {
            index: 0,
            backing_depth: 0,
            target_depth: 1,
            publishes: false,
            column_len: 2 * span,
            backing: SegBacking::Ext(values.clone()),
        };
        for row in 0..rows {
            let (s0, s1) = one_step.endpoints(0, row, rows, &challenges);
            assert_eq!(s0, fold(values[row], values[row + span], challenges[0]));
            assert_eq!(
                s1,
                fold(values[rows + row], values[rows + row + span], challenges[0])
            );
        }

        let two_step = SegHostWindow {
            index: 0,
            backing_depth: 0,
            target_depth: 2,
            publishes: false,
            column_len: 4 * span,
            backing: SegBacking::Ext(values.clone()),
        };
        for row in 0..rows {
            // Level 1 is the WIDER stride (2 * span) and the EARLIER challenge;
            // level 2 the narrower (span) and the later one.
            let low = fold(values[row], values[row + 2 * span], challenges[0]);
            let high = fold(values[row + span], values[row + 3 * span], challenges[0]);
            let (s0, _) = two_step.endpoints(0, row, rows, &challenges);
            assert_eq!(s0, fold(low, high, challenges[1]));
        }
    }

    /// The delta sets are exactly what `lower_bwd_seg` accepts: zero, one, and the
    /// round's own fold depth, never a distance in between.
    #[test]
    fn the_e4_delta_sets_are_the_supported_catch_ups() {
        assert_eq!(e4_deltas(0), vec![0]);
        assert_eq!(e4_deltas(1), vec![0, 1]);
        assert_eq!(e4_deltas(2), vec![0, 1, 2]);
        assert_eq!(e4_deltas(3), vec![0, 1, 3]);
        // Past the publication depth every DRAM source has already published, so
        // the resolver set collapses to the steady state.
        assert_eq!(e4_deltas(4), vec![0, 1]);
    }

    /// The corpus really reaches every live term class of both regimes, which is
    /// what makes the ladder's class coverage a measurement rather than a hope.
    #[test]
    fn the_ladder_corpus_reaches_every_live_term_class() {
        use gkr_eval_isa::bwd::coeff::lean::decode_program;
        use gkr_eval_isa::bwd::coeff::lean::{LEAN_CONT_OPCODES, LEAN_R0_OPCODES};

        let mut r0 = std::collections::BTreeSet::new();
        let mut cont = std::collections::BTreeSet::new();
        for circuit in SEG_LAYOUTS {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let coord = lean_coordinate(circuit, 0, regime);
                let table = match regime {
                    BwdRegime::R0 => LEAN_R0_OPCODES,
                    BwdRegime::Ext => LEAN_CONT_OPCODES,
                };
                for record in decode_program(&coord.artifact.program).expect("decode") {
                    let category = table
                        .iter()
                        .find(|(class, _)| *class == u16::from(record.class))
                        .map(|(_, category)| *category)
                        .unwrap_or_else(|| panic!("class {} is dead in {regime:?}", record.class));
                    match regime {
                        BwdRegime::R0 => r0.insert(category),
                        BwdRegime::Ext => cont.insert(category),
                    };
                }
            }
        }
        eprintln!("[seg-ladder] R0 classes {r0:?}, continuation classes {cont:?}");
        assert_eq!(
            r0,
            [
                TermCategory::C0LinearBf,
                TermCategory::C0LinearE4,
                TermCategory::C2ProductBfBf,
                TermCategory::C2ProductBfE4,
                TermCategory::C2ProductE4E4,
            ]
            .into_iter()
            .collect(),
            "the R0 ladder must reach every live R0 class; C2ProductBfE4 in particular is where \
             the BF-first operand order the kernel trusts is exercised"
        );
        assert_eq!(
            cont,
            [TermCategory::C0LinearE4, TermCategory::DualProductE4]
                .into_iter()
                .collect(),
            "the continuation ladder must reach both live continuation classes"
        );
    }

    /// The window mix the ladder needs really exists in the corpus: a base-field
    /// window (the BF pyramid), an E4 window (the chain step) and a procedural one
    /// (row synthesis). A corpus without all three would make part of the matrix
    /// vacuous, so it is asserted rather than assumed.
    #[test]
    fn the_ladder_corpus_carries_every_window_origin() {
        let mut base = 0usize;
        let mut ext = 0usize;
        let mut procedural = 0usize;
        for circuit in SEG_LAYOUTS {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let coord = lean_coordinate(circuit, 0, regime);
                for window in &coord.artifact.binding.windows {
                    match (window.procedural_kind(), window.backing_field()) {
                        (Some(_), _) => procedural += 1,
                        (None, FieldKind::Base) => base += 1,
                        (None, FieldKind::Ext) => ext += 1,
                    }
                }
            }
        }
        eprintln!(
            "[seg-ladder] window origins over the four circuits: {base} base, {ext} ext, \
             {procedural} procedural"
        );
        assert!(base > 0, "no base-field window: the BF pyramid is untested");
        assert!(
            procedural > 0,
            "no procedural window: row synthesis is untested"
        );
    }
}
