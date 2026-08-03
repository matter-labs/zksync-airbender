//! The backward VM's lean coordinate, compiled at runtime in production.
//!
//! The bench builds its `CoeffLayer` through
//! [`seg_compile::lean_layer`](super::seg_compile), which deserializes a
//! committed layout JSON from an `env!("CARGO_MANIFEST_DIR")` path and caches
//! the lowered DAG. None of that exists in a shipped binary.
//!
//! # Why no committed lean artifact
//!
//! Not because the order is trivial. `compile_lean_coordinate` is
//! `lower_lean_layer` + `order_terms` (R0) or `order_atoms` (Ext), and
//! `order_rows` (`gkr_eval_isa/src/bwd/coeff/order.rs`) is a real greedy
//! **source-affinity clustering** pass — it repeatedly emits the unplaced row
//! sharing the most distinct sources with the union of the last
//! `AFFINITY_WINDOW = 8` emitted rows. That clustering is what gives the eval
//! loop its locality; it is load-bearing.
//!
//! What removes the artifact is that it is **deterministic**: no stochastic or
//! multi-trial search (the c2–c16 order-genome search is gone), so the same DAG
//! in gives the same order out and production can recompute rather than load.
//! `compiling_the_same_coordinate_twice_gives_the_same_program` is what holds
//! that property to account.
//!
//! The cost this defers is host time on the scheduling thread, once per process,
//! behind a `lower_dag` over a layout that can be tens of megabytes.
//! `report_the_coordinate_compile_time` prints it. If it grows material for the
//! corpus monsters, a committed artifact becomes worth having for TIME — a later
//! decision this module measures the input to rather than pre-empts.
//!
//! The artifact must be the RAW one, before
//! `transform::normalize_compiled_circuit_for_gpu`, for the same reason as the
//! forward VM: normalization rewrites scratch-backed addresses in gate
//! relations, and the DAG the coordinate is compiled against must be the one the
//! source binder's `ReadPlace`s refer to.

use std::collections::{BTreeMap, HashMap};
#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use gkr_eval_isa::bwd::coeff::lean_artifact::{
    compile_lean_coordinate, lower_lean_layer, LeanCoordinateArtifact,
};
use gkr_eval_isa::bwd::coeff::model::CoeffLayer;
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;

use crate::primitives::field::BF;
use crate::witness::circuit_type::CircuitType;
use crate::upstream::{
    lower_dag, validate_dag, BwdRegime, DagLayer, FieldKind, GKRCircuitArtifact, ReadPlace,
};

/// One circuit's lowered DAG layers plus its whole-circuit cross-layer field map
/// — everything `compile_lean_coordinate` needs beyond the layer index.
pub(crate) struct LoweredCircuit {
    pub(crate) layers: Vec<DagLayer>,
    pub(crate) cross_fields: HashMap<ReadPlace, FieldKind>,
}

/// One coordinate plus the `CoeffLayer` it was lowered from.
///
/// The artifact deliberately carries neither the coefficient RECIPES (the bank's
/// content, a layer property) nor the immediate table — in the bench only the
/// bridge that built both still holds them ([`BwdSegRoundBinding::immediates`]'s
/// doc). Production's launcher needs the recipes to build the device bank fill,
/// so the compiled slice keeps the layer beside the coordinate.
///
/// [`BwdSegRoundBinding::immediates`]: super::seg_lower::BwdSegRoundBinding::immediates
pub(crate) struct CompiledSlice {
    pub(crate) coord: LeanCoordinateArtifact,
    pub(crate) layer: CoeffLayer,
}

/// Index a regime for the cache key. An explicit match, so an upstream regime
/// added later fails to compile here rather than colliding with an existing key.
fn regime_key(regime: BwdRegime) -> u8 {
    match regime {
        BwdRegime::R0 => 0,
        BwdRegime::Ext => 1,
    }
}

/// The circuit's lowered DAG, once per process.
///
/// Separate from the slice cache because the lowering is a per-CIRCUIT cost that
/// every `(layer, regime)` coordinate shares: `report_the_compile_time_
/// projection_over_the_corpus` measures 34.5 ms of lowering across the corpus
/// against 232.0 ms of coordinate compiles, and lowering per slice instead would
/// multiply the first figure by the number of slices.
///
/// Keyed by circuit like the slices are: a process may prove several, and an
/// unkeyed lowering would hand the second circuit the first one's DAG — the
/// binder would then resolve addresses against the wrong layout.
fn lowered_circuit(
    circuit_type: CircuitType,
    artifact: &GKRCircuitArtifact<BF>,
) -> Result<&'static LoweredCircuit, String> {
    static LOWERED: Mutex<BTreeMap<CircuitType, Result<&'static LoweredCircuit, String>>> =
        Mutex::new(BTreeMap::new());
    let mut lowered = LOWERED
        .lock()
        .expect("the lowering cache mutex is never poisoned");
    lowered
        .entry(circuit_type)
        .or_insert_with(|| {
            #[cfg(test)]
            LOWERINGS.fetch_add(1, Ordering::Relaxed);
            lower_and_validate(artifact).map(|lowered| &*Box::leak(Box::new(lowered)))
        })
        .clone()
}

/// Counts lowerings so `the_lowering_is_shared_by_every_slice_of_the_circuit`
/// can assert the sharing rather than infer it from a timing.
#[cfg(test)]
static LOWERINGS: AtomicUsize = AtomicUsize::new(0);

#[cfg(test)]
pub(crate) fn lowerings_for_test() -> usize {
    LOWERINGS.load(Ordering::Relaxed)
}

/// One `(layer, regime)` coordinate and its layer, compiled once per process.
///
/// Cached like the forward VM's program, but keyed — R0 and Ext are different
/// programs over one layer, and each main layer has its own pair. Deliberately
/// a SEPARATE cache from `forward::vm::program`'s: caches of the same lowering
/// are cheaper than a cross-module dependency, and each entry is only populated
/// when its coordinate is selected.
///
/// Entries are leaked deliberately: the cache is process-lifetime by
/// construction (bounded by layers x regimes) and callers hold `&'static`, the
/// same contract the previous `OnceLock` pair gave them. A compile FAILURE is
/// cached too, so a coordinate that cannot compile is not retried on every
/// proof.
pub(crate) fn compiled_slice(
    circuit_type: CircuitType,
    artifact: &GKRCircuitArtifact<BF>,
    layer_index: usize,
    regime: BwdRegime,
) -> Result<&'static CompiledSlice, String> {
    static SLICES: Mutex<
        BTreeMap<(CircuitType, usize, u8), Result<&'static CompiledSlice, String>>,
    > = Mutex::new(BTreeMap::new());

    let key = (circuit_type, layer_index, regime_key(regime));
    // Held across the compile on purpose: two threads racing the same
    // coordinate would otherwise both compile it and leak the loser. Plan build
    // is single-threaded, so this never contends in production.
    let mut slices = SLICES.lock().expect("the slice cache mutex is never poisoned");
    slices
        .entry(key)
        .or_insert_with(|| {
            let lowered = lowered_circuit(circuit_type, artifact)?;
            let coord = compile_from_dag(lowered, layer_index, regime)?;
            // The same lowering `compile_lean_coordinate` runs internally —
            // deterministic (`compiling_the_same_coordinate_twice_gives_the_same_
            // program`), so the layer here IS the one the coordinate came from.
            let canonical = &lowered.layers[layer_index];
            let (layer, _) = lower_lean_layer(canonical, &lowered.cross_fields, regime)
                .map_err(|e| format!("lower_lean_layer: {e:?}"))?;
            Ok(&*Box::leak(Box::new(CompiledSlice { coord, layer })))
        })
        .clone()
}

/// `lower_dag` -> `validate` -> the cross-layer field map, over the RAW artifact.
pub(crate) fn lower_and_validate(
    artifact: &GKRCircuitArtifact<BF>,
) -> Result<LoweredCircuit, String> {
    let dag = lower_dag(artifact).map_err(|e| format!("lower_dag: {e}"))?;
    validate_dag(&dag).map_err(|e| format!("validate: {e}"))?;
    let cross_fields = build_cross_layer_field_map(&dag);
    Ok(LoweredCircuit {
        layers: dag.layers,
        cross_fields,
    })
}

/// Compile one `(layer, regime)` coordinate from an already-lowered circuit.
pub(crate) fn compile_from_dag(
    lowered: &LoweredCircuit,
    layer_index: usize,
    regime: BwdRegime,
) -> Result<LeanCoordinateArtifact, String> {
    let canonical = lowered.layers.get(layer_index).ok_or_else(|| {
        format!(
            "layer {layer_index} is outside the circuit's {} lowered layers",
            lowered.layers.len()
        )
    })?;
    compile_lean_coordinate(
        "add_sub_lui_auipc_mop",
        layer_index,
        canonical,
        &lowered.cross_fields,
        regime,
    )
    .map_err(|e| format!("compile_lean_coordinate: {e:?}"))
}

/// The whole chain, over an explicit coordinate so the negative cases are
/// testable.
pub(crate) fn compile_coordinate(
    artifact: &GKRCircuitArtifact<BF>,
    layer_index: usize,
    regime: BwdRegime,
) -> Result<LeanCoordinateArtifact, String> {
    let lowered = lower_and_validate(artifact)?;
    compile_from_dag(&lowered, layer_index, regime)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The cache key every test here uses — the circuit the artifact belongs to.
    const ADD_SUB: CircuitType = CircuitType::Unrolled(
        crate::witness::circuit_type::UnrolledCircuitType::NonMemory(
            crate::witness::circuit_type::UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        ),
    );

    fn add_sub_artifact() -> GKRCircuitArtifact<BF> {
        crate::prover::tests::deserialize_json_for_test(
            "cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json",
        )
    }

    /// The bench builds its `CoeffLayer` by deserializing a committed layout from
    /// a source-tree path. This is the same chain over the artifact production
    /// already holds, which is what removes the need for a committed lean file.
    #[test]
    fn the_lean_r0_coordinate_compiles_from_the_production_artifact() {
        let artifact = add_sub_artifact();
        let coord = compile_coordinate(&artifact, 0, BwdRegime::R0)
            .expect("add_sub L0 R0 must compile from the production artifact");

        assert_eq!(coord.regime.regime(), BwdRegime::R0);
        assert_eq!(coord.layer, 0);
        // R0 reads unfolded polynomials — nothing has been folded yet.
        assert_eq!(coord.target_depth, 0);
        assert!(!coord.order.is_empty());
    }

    /// Determinism is the property that lets production recompute the coordinate
    /// instead of loading a committed artifact. `order_rows` is a real greedy
    /// source-affinity clustering pass, so this is not a trivial claim — if it
    /// ever stops holding, a committed artifact becomes mandatory.
    #[test]
    fn compiling_the_same_coordinate_twice_gives_the_same_program() {
        let artifact = add_sub_artifact();
        let a = compile_coordinate(&artifact, 0, BwdRegime::R0).unwrap();
        let b = compile_coordinate(&artifact, 0, BwdRegime::R0).unwrap();
        assert_eq!(a.order, b.order, "the committed order must be reproducible");
        assert_eq!(a.program, b.program);
        assert_eq!(a.binding, b.binding);
    }

    /// R0 and Ext are different programs over the same layer, which is why the
    /// switch names `(layer, regime)` pairs rather than layers.
    #[test]
    fn r0_and_ext_are_different_coordinates_of_one_layer() {
        let artifact = add_sub_artifact();
        let r0 = compile_coordinate(&artifact, 0, BwdRegime::R0).unwrap();
        let ext = compile_coordinate(&artifact, 0, BwdRegime::Ext).unwrap();
        assert_ne!(r0.target_depth, ext.target_depth);
        assert_ne!(r0.program, ext.program);
    }

    /// The process-wide cache is keyed by `(layer, regime)`: repeated calls
    /// return the same `&'static` slice, and each key carries its own program.
    /// The launcher needs both regimes when `0:R0,0:Ext` is selected together,
    /// and one entry per layer once more than one layer is selected.
    #[test]
    fn compiled_slices_are_cached_per_layer_and_regime() {
        let artifact = add_sub_artifact();
        let r0 = compiled_slice(ADD_SUB, &artifact, 0, BwdRegime::R0).unwrap();
        let ext = compiled_slice(ADD_SUB, &artifact, 0, BwdRegime::Ext).unwrap();
        assert!(std::ptr::eq(
            r0,
            compiled_slice(ADD_SUB, &artifact, 0, BwdRegime::R0).unwrap()
        ));
        assert!(std::ptr::eq(
            ext,
            compiled_slice(ADD_SUB, &artifact, 0, BwdRegime::Ext).unwrap()
        ));
        assert_eq!(r0.coord.regime.regime(), BwdRegime::R0);
        assert_eq!(ext.coord.regime.regime(), BwdRegime::Ext);
        assert_ne!(r0.coord.program, ext.coord.program);
        // The layer rides beside the coordinate for the bank fill and, in Ext,
        // for `c_init` pass-through.
        assert_eq!(ext.layer.regime, BwdRegime::Ext);
    }

    /// The layer is part of the cache KEY, not a constant: asking for layer 1
    /// must not hand back layer 0's program. Before the re-key both regimes'
    /// caches compiled layer 0 unconditionally, so this is the assertion that
    /// distinguishes a per-layer cache from a per-regime one.
    #[test]
    fn a_slice_carries_the_layer_it_was_asked_for() {
        let artifact = add_sub_artifact();
        for layer in 0..artifact.layers.len().min(4) {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let slice = compiled_slice(ADD_SUB, &artifact, layer, regime)
                    .unwrap_or_else(|e| panic!("layer {layer} {regime:?} must compile: {e}"));
                assert_eq!(slice.coord.layer, layer, "coordinate layer");
                assert_eq!(slice.coord.regime.regime(), regime, "coordinate regime");
                assert!(std::ptr::eq(
                    slice,
                    compiled_slice(ADD_SUB, &artifact, layer, regime).unwrap()
                ));
            }
        }
    }

    /// `lower_dag` is a per-CIRCUIT cost that every one of its `(layer, regime)`
    /// coordinates shares. Keyed per slice instead, the corpus projection's
    /// 34.5 ms of lowering would become ~324 ms of duplicated work — more than
    /// the coordinate compiles it exists to feed.
    ///
    /// Asserted as a DELTA because the cache is process-wide and another test
    /// may already have populated it: N slice requests must trigger at most one
    /// lowering, whatever ran first.
    #[test]
    fn the_lowering_is_shared_by_every_slice_of_the_circuit() {
        let artifact = add_sub_artifact();
        let before = lowerings_for_test();
        for layer in 0..artifact.layers.len().min(4) {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                compiled_slice(ADD_SUB, &artifact, layer, regime).unwrap();
            }
        }
        let lowerings = lowerings_for_test() - before;
        assert!(
            lowerings <= 1,
            "8 slice requests triggered {lowerings} lowerings; the lowering must be shared"
        );
    }

    #[test]
    fn a_layer_outside_the_circuit_is_rejected() {
        let artifact = add_sub_artifact();
        let beyond = artifact.layers.len();
        assert!(compile_coordinate(&artifact, beyond, BwdRegime::R0).is_err());
    }

    /// `order_rows` runs on the scheduling thread behind a `lower_dag` over a
    /// layout that can be tens of megabytes. Report the cost rather than absorb
    /// it: it is off the A/B's measured path (the harness warms up first) but on
    /// the first proof's path, and it is the input to whether a committed lean
    /// artifact is worth having for TIME.
    #[test]
    fn report_the_coordinate_compile_time() {
        let artifact = add_sub_artifact();
        let start = std::time::Instant::now();
        let dag = lower_and_validate(&artifact).unwrap();
        let lowered_ms = start.elapsed().as_secs_f64() * 1e3;

        let start = std::time::Instant::now();
        let coord = compile_from_dag(&dag, 0, BwdRegime::R0).unwrap();
        let coordinate_ms = start.elapsed().as_secs_f64() * 1e3;

        eprintln!(
            "[bwd-vm-compile] add_sub L0 R0: lower_dag+validate {lowered_ms:.1} ms, \
             coordinate {coordinate_ms:.1} ms, {} terms ordered",
            coord.order.len()
        );
    }

    /// What the runtime-compile decision costs at CORPUS scale, which is the
    /// only scale at which it can stop being free.
    ///
    /// The single-layer report above says nothing about the shape that matters:
    /// the cost is paid per circuit for `lower_dag` and per `(layer, regime)`
    /// for the coordinate, so it grows with the product, and the heavy layouts
    /// are ~17x add_sub's. This walks every layer of every circuit that has a
    /// committed GKR layout, both regimes, and prints the per-circuit and total
    /// host time a process would pay if the VM owned everything.
    ///
    /// Deserialization is reported SEPARATELY and excluded from the totals:
    /// production is handed the artifact, it does not parse JSON. `#[ignore]`d
    /// because it reads every layout in the corpus (~13 MB of JSON) and takes
    /// far longer than a unit test should.
    #[test]
    #[ignore]
    fn report_the_compile_time_projection_over_the_corpus() {
        /// Every circuit with a committed GKR layout, heaviest layouts last.
        const CIRCUITS: &[&str] = &[
            "inits_and_teardowns",
            "inits_and_teardowns_preprocessed",
            "mem_word_only",
            "mem_subword_only",
            "add_sub_lui_auipc_mop",
            "jump_branch_slt",
            "shift_binop",
            "unsigned_mul_div",
            "blake2_g_function",
            "unified_reduced_machine",
            "keccak_special5",
            "blake2_with_extended_control",
            "bigint_with_extended_control",
        ];

        let mut total_lower_ms = 0.0f64;
        let mut total_coord_ms = 0.0f64;
        let mut total_layers = 0usize;
        eprintln!(
            "[bwd-vm-compile-projection] circuit  layers  lower_ms  coord_ms  \
             per_layer_ms  (deserialize_ms)"
        );
        for name in CIRCUITS {
            let start = std::time::Instant::now();
            let artifact: GKRCircuitArtifact<BF> = crate::prover::tests::deserialize_json_for_test(
                &format!("cs/compiled_circuits/{name}_layout_gkr.json"),
            );
            let deserialize_ms = start.elapsed().as_secs_f64() * 1e3;

            let start = std::time::Instant::now();
            let lowered = match lower_and_validate(&artifact) {
                Ok(lowered) => lowered,
                Err(e) => {
                    eprintln!("[bwd-vm-compile-projection] {name}: lower failed: {e}");
                    continue;
                }
            };
            let lower_ms = start.elapsed().as_secs_f64() * 1e3;

            // Both regimes of every layer: the full bill if the VM owned the
            // whole circuit. A layer the compiler rejects is counted as free
            // and named, not silently skipped.
            let layers = lowered.layers.len();
            let start = std::time::Instant::now();
            let mut rejected = 0usize;
            for layer in 0..layers {
                for regime in [BwdRegime::R0, BwdRegime::Ext] {
                    if compile_from_dag(&lowered, layer, regime).is_err() {
                        rejected += 1;
                    }
                }
            }
            let coord_ms = start.elapsed().as_secs_f64() * 1e3;

            eprintln!(
                "[bwd-vm-compile-projection] {name:>32}  {layers:>6}  {lower_ms:>8.1}  \
                 {coord_ms:>8.1}  {:>12.2}  ({deserialize_ms:.0})",
                coord_ms / (layers as f64).max(1.0),
            );
            if rejected != 0 {
                eprintln!(
                    "[bwd-vm-compile-projection] {name}: {rejected} of {} (layer, regime) pairs \
                     did not compile",
                    layers * 2
                );
            }
            total_lower_ms += lower_ms;
            total_coord_ms += coord_ms;
            total_layers += layers;
        }

        eprintln!(
            "[bwd-vm-compile-projection] TOTAL over {} circuits, {total_layers} layers, both \
             regimes: lower {total_lower_ms:.1} ms + coordinates {total_coord_ms:.1} ms = \
             {:.1} ms of host time",
            CIRCUITS.len(),
            total_lower_ms + total_coord_ms,
        );
        eprintln!(
            "[bwd-vm-compile-projection] note: one `lower_dag` per circuit is shared by all its \
             layers and regimes ONLY if the cache is keyed that way — today each regime's \
             `OnceLock` re-lowers, so a naive per-(layer, regime) cache would pay lower_dag \
             {} times instead of {}",
            total_layers * 2,
            CIRCUITS.len(),
        );
    }
}
