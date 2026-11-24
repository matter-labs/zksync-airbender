use prover::cs::gkr_compiler::GKRCircuitArtifact;
use prover::field::Proth120;
use prover::worker::Worker;
use unified_reduced_machine_proth120::l1_wrap::l1_wrap_setup_from_artifact;
use unified_reduced_machine_proth120::L1WrapSetup;

pub use prover::gkr::prover_config::example_configs::l1_wrap::ETHPROOFS_TRACE_LEN_LOG2 as TRACE_LEN_LOG2;
pub use unified_reduced_machine_proth120::l1_wrap::{witness_eval_fn, ROM};

pub const LAYOUT_JSON: &str = include_str!("../generated/layout.json");

pub fn circuit_artifact() -> GKRCircuitArtifact<Proth120> {
    serde_json::from_str(LAYOUT_JSON).expect("embedded 2^22 Proth120 unified layout")
}

pub fn l1_wrap_setup(binary: &[u32], text: &[u32], worker: &Worker) -> L1WrapSetup {
    let circuit = circuit_artifact();
    assert_eq!(circuit.trace_len, 1 << TRACE_LEN_LOG2);
    l1_wrap_setup_from_artifact(circuit, binary, text, worker)
}
