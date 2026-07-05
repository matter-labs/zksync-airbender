//! Production-path compile of a fwd-VM `CompiledCircuit` from committed
//! fixtures (Task 1). `gkr_eval_isa`/`cs` are dev-dependencies here (the
//! module is `cfg(all(test, feature = "bench"))`), so the crate's
//! `crate::upstream` re-export convention does not apply — see
//! `bench_interp/lower.rs:1-4`.

use cs::definitions::GKRAddress;
use cs::gkr_compiler::dag_ir::{lower_dag, validate, validate_circuit_schedule, CircuitSchedule, DagCircuit, ReadPlace};
use cs::gkr_compiler::GKRCircuitArtifact;
use gkr_eval_isa::fwd::compile::{compile_circuit, load_committed_schedule, CompiledCircuit};
use gkr_eval_isa::fwd::context::CompiledLayer;
use gkr_eval_isa::fwd::encode::{decode, encode};

use crate::primitives::field::BF;

/// Result of driving one committed circuit fixture through the stage-3
/// (schedule-driven) production compile chain. Later tasks lower `compiled`
/// into the device ABI.
pub(crate) struct FwdVmCircuit {
    pub dag: DagCircuit,
    pub sched: CircuitSchedule,
    pub artifact: GKRCircuitArtifact<BF>,
    pub compiled: CompiledCircuit,
}

/// Load + compile one committed circuit fixture by stem (e.g.
/// `"add_sub_lui_auipc_mop"`) through the exact production chain
/// (`gkr_eval_isa/tests/stage3_schedule_driven.rs:357` is the authority for
/// this sequence): `lower_dag` -> `validate` -> `load_committed_schedule` ->
/// `validate_circuit_schedule` -> `compile_circuit`. Panics with the stem
/// named in the message on any failure.
pub(crate) fn load_fwd_vm_circuit(stem: &str) -> FwdVmCircuit {
    let artifact: GKRCircuitArtifact<BF> = crate::prover::tests::deserialize_json_for_test(
        &format!("cs/compiled_circuits/{stem}_layout_gkr.json"),
    );
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{stem}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{stem}] validate: {e}"));

    let schedule_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits")
        .join(format!("{stem}_schedule_b16_gkr.json"));
    let sched = load_committed_schedule(&schedule_path)
        .unwrap_or_else(|e| panic!("[{stem}] load_committed_schedule: {e:?}"));
    validate_circuit_schedule(&dag, &sched)
        .unwrap_or_else(|e| panic!("[{stem}] validate_circuit_schedule: {e}"));
    let compiled = compile_circuit(&dag, &sched, &artifact)
        .unwrap_or_else(|e| panic!("[{stem}] compile_circuit: {e:?}"));

    FwdVmCircuit { dag, sched, artifact, compiled }
}

/// Invert `lower_dag`'s `map_address` (`cs/src/gkr_compiler/dag_ir/lower/mod.rs:99`):
/// a DAG-IR `ReadPlace` maps back to the artifact `GKRAddress` its read was
/// lowered from. This is the single address mapping both the G-CPU D2H capture
/// (Task 2) and Task 3's device lowering consume. `VirtualSetup` is never a
/// `ReadPlace` (it lowers to `SourceKind::VirtualSetup`, resolved separately),
/// so there is no virtual-setup arm; every `ReadPlace` variant is total here.
pub(crate) fn read_place_to_gkr_address(
    place: &ReadPlace,
    _artifact: &GKRCircuitArtifact<BF>,
) -> GKRAddress {
    match *place {
        ReadPlace::BaseLayerMemory { column } => GKRAddress::BaseLayerMemory(column),
        ReadPlace::BaseLayerWitness { column } => GKRAddress::BaseLayerWitness(column),
        ReadPlace::Setup { column } => GKRAddress::Setup(column),
        ReadPlace::Scratch { slot } => GKRAddress::ScratchSpace(slot),
        ReadPlace::LayerOutput { layer, offset } => GKRAddress::InnerLayer { layer, offset },
        ReadPlace::CacheOutput { layer, offset } => GKRAddress::Cached { layer, offset },
    }
}

/// Encode one compiled layer's program (spec §5 canonical pre-gate: encode,
/// then round-trip decode and assert equality) and return the LDC-bound
/// lane count for the size probe (spec §4).
pub(crate) fn encoded_lanes(cl: &CompiledLayer) -> Vec<u16> {
    let lanes = encode(&cl.program).unwrap();
    let decoded = decode(&lanes).unwrap();
    assert_eq!(decoded, cl.program, "encode/decode round-trip mismatch");
    lanes
}
