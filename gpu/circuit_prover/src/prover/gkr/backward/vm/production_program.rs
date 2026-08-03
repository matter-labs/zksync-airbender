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

use std::collections::HashMap;
use std::sync::OnceLock;

use gkr_eval_isa::bwd::coeff::lean_artifact::{compile_lean_coordinate, LeanCoordinateArtifact};
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;

use crate::primitives::field::BF;
use crate::upstream::{
    lower_dag, validate_dag, BwdRegime, DagLayer, FieldKind, GKRCircuitArtifact, ReadPlace,
};

/// One circuit's lowered DAG layers plus its whole-circuit cross-layer field map
/// — everything `compile_lean_coordinate` needs beyond the layer index.
pub(crate) struct LoweredCircuit {
    pub(crate) layers: Vec<DagLayer>,
    pub(crate) cross_fields: HashMap<ReadPlace, FieldKind>,
}

/// The add_sub L0 R0 coordinate, compiled once per process.
///
/// Cached like the forward VM's program. Deliberately a SEPARATE `OnceLock` from
/// `forward::vm::program`'s: two caches of the same lowering are cheaper than a
/// cross-module dependency, and the forward one is only populated when the
/// forward switch is on.
pub(crate) fn compiled_r0_coordinate(
    artifact: &GKRCircuitArtifact<BF>,
) -> Result<&'static LeanCoordinateArtifact, String> {
    static COORD: OnceLock<Result<LeanCoordinateArtifact, String>> = OnceLock::new();
    COORD
        .get_or_init(|| compile_coordinate(artifact, 0, BwdRegime::R0))
        .as_ref()
        .map_err(Clone::clone)
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
}
