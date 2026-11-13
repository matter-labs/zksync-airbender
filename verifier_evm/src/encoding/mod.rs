//! Calldata format F1 for the single-transaction L1 wrap verifier
//! with transcript-preserving compression. The verifier reconstructs omitted values
//! before absorbing them. See `verifier_evm/gkr_transcript_reference.md`
//! for encoding invariants and verification/producer pointers.
//!
//! F1 stores GKR then WHIR. Registers are LE u32; PoW nonces are BE u64.
//! Field runs pack canonical 123-bit values MSB-first; digests use the 25-byte
//! prefix of their big-endian words. The final PC, the inits/teardowns top bits
//! and the setup cap are deployment constants.

mod digest;
mod gkr;
mod params;
mod replay;
mod runs;
mod whir;

use std::collections::BTreeMap;

use prover::gkr::prover::OperationMode;
use prover::gkr::prover_config::ProverConfig;

pub use digest::{digest_wire, merkle_node, merkle_reduce};
pub use gkr::split_round;
pub use params::FormatParams;
pub(crate) use params::Geometry;

pub use replay::{replay_gkr_points, GkrReplay, LayerPoints};
pub use runs::{fe_run_len, ts_run_len, write_fe_run, write_ts_run};

use crate::seed::{Circuit, Proof};

/// F1 single-tx calldata and the `(offset, length)` of every named field.
#[derive(Clone, Debug)]
pub struct SingleTxCalldata {
    pub bytes: Vec<u8>,
    pub fields: BTreeMap<String, (usize, usize)>,
    /// Length of the GKR section (the WHIR section starts here).
    pub gkr_bytes: usize,
}

#[derive(Default)]
pub(crate) struct Writer {
    bytes: Vec<u8>,
    fields: BTreeMap<String, (usize, usize)>,
}

impl Writer {
    pub(crate) fn put(&mut self, name: impl Into<String>, data: &[u8]) {
        let name = name.into();
        let prev = self
            .fields
            .insert(name.clone(), (self.bytes.len(), data.len()));
        assert!(prev.is_none(), "duplicate field {name}");
        self.bytes.extend_from_slice(data);
    }
}

/// Panics unless `circuit`, `aux` and `proof` have the shape `params` describes.
fn check_profile(
    circuit: &Circuit,
    proof: &Proof,
    aux: &OperationMode,
    config: &ProverConfig,
    params: &Geometry,
) {
    assert!(
        matches!(aux, OperationMode::SingleChunk { .. }),
        "expected single-chunk operation mode"
    );
    assert!(
        config.pack_log2() > 0 && config.merged_memory_and_witness(),
        "expected packed merged prover config"
    );
    assert_eq!(
        circuit.trace_len,
        1 << params.trace_log2,
        "profile trace log differs from the circuit"
    );
    for v in proof.final_explicit_evaluations.values() {
        for evals in v {
            assert_eq!(
                evals.len(),
                1 << params.explicit_output_log2,
                "profile explicit output log differs from the proof"
            );
        }
    }
    let ws = &proof.whir_proof.whir_schedule;
    assert_eq!(
        ws.fold_steps(),
        params.folds,
        "profile folds differ from the proof"
    );
    assert_eq!(
        ws.queries_per_round(),
        params.queries,
        "profile queries differ from the proof"
    );
    assert_eq!(
        ws.cap_size,
        params.cap(),
        "profile cap differs from the proof"
    );
    assert_eq!(
        ws, &config.whir_schedule,
        "profile WHIR schedule differs from the proof"
    );
    let setup_path = proof.whir_proof.setup_commitment.queries[0].path.len();
    assert!(
        params.setup_frontier_skip() <= setup_path,
        "profile setup frontier lies below the setup leaves"
    );
}

/// The F1 single-tx calldata of `proof`. Panics when the proof does not fit `params`, when a
/// round polynomial is not `e_z(X)` times a quadratic, or when the reconstructed
/// batching challenge does not match the proof's first WHIR sumcheck claim.
pub fn encode_single_tx(
    circuit: &Circuit,
    proof: &Proof,
    aux: &OperationMode,
    config: &ProverConfig,
    params: &FormatParams,
) -> SingleTxCalldata {
    let params = &Geometry::from_config(config, params);
    check_profile(circuit, proof, aux, config, params);
    let replay = replay_gkr_points(circuit, proof, aux, config);
    let mut w = Writer::default();
    gkr::encode_gkr(&mut w, circuit, proof, aux, params, &replay);
    let gkr_bytes = w.bytes.len();
    whir::encode_whir(&mut w, proof, params);
    SingleTxCalldata {
        bytes: w.bytes,
        fields: w.fields,
        gkr_bytes,
    }
}
