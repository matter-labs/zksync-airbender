//! Production-path compile of a fwd-VM `CompiledCircuit` from committed
//! fixtures (Task 1). `gpu_gkr_compiler`/`cs` are dev-dependencies here (the
//! module is `cfg(all(test, feature = "bench"))`), so the crate's
//! `crate::upstream` re-export convention does not apply.

use cs::gkr_compiler::GKRCircuitArtifact;
use gkr_eval_ir::{lower_dag, validate, DagCircuit};
use gpu_gkr_compiler::forward::compile::{load_committed_schedule, CompiledCircuit};
use gpu_gkr_compiler::forward::context::CompiledLayer;
use gpu_gkr_compiler::forward::encode::{decode, encode};
use gpu_gkr_compiler::{compile_forward, validate_forward_artifact, ForwardSearchArtifact};

use crate::primitives::field::BF;

/// Result of driving one committed circuit fixture through the stage-3
/// (schedule-driven) production compile chain. Later tasks lower `compiled`
/// into the device ABI.
pub(crate) struct FwdVmCircuit {
    pub dag: DagCircuit,
    pub sched: ForwardSearchArtifact,
    pub artifact: GKRCircuitArtifact<BF>,
    pub compiled: CompiledCircuit,
}

/// Load + compile one committed circuit fixture by stem (e.g.
/// `"add_sub_lui_auipc_mop"`) through the exact production chain
/// (`gpu_gkr_compiler/tests/stage3_schedule_driven.rs:357` is the authority for
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
    validate_forward_artifact(&dag, &sched)
        .unwrap_or_else(|e| panic!("[{stem}] validate_forward_artifact: {e}"));
    let compiled =
        compile_forward(&dag, &sched).unwrap_or_else(|e| panic!("[{stem}] compile_forward: {e:?}"));

    FwdVmCircuit {
        dag,
        sched,
        artifact,
        compiled,
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
