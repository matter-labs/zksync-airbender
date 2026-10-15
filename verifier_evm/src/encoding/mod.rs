//! Calldata format F1 for the single-transaction L1 wrap verifier
//! (`orange/.agents/specs/2026-10-15-w7b-gas-levers-design.md` §2): a re-encoding of the v0
//! streams (`crate::flatten`) whose omitted values the verifier recomputes, so it absorbs the
//! v0 bytes unchanged.
//!
//! Single-tx layout: `GKR section ‖ WHIR section`, in transcript order.
//! - GKR: registers (32 × LE u32), `TS-run` of the 32 register timestamps and the final
//!   timestamp, top bits (LE u32), memory cap (`DIGEST`s), external PoW nonce (BE u64),
//!   `FE-run` of the explicit output evaluations, per dimension-reducing layer `FE-run(2k)` of the
//!   round `(b, c)` pairs (E1) and `FE-run` of the LSB lines, per circuit layer `FE-run(2t)` of
//!   `(b, c)` and `FE-run` of the at-point evals, WHIR batching PoW nonce (BE u64). The final PC
//!   and the setup cap are deployment constants.
//! - WHIR, per round: `FE-run` of the sumcheck `(c0, c2)` pairs (E2); intermediate rounds: cap
//!   (`DIGEST`s), OOD value (BE16), PoW nonce (BE u64); the final round: `FE-run` of the
//!   monomials, PoW nonce; then per query in draw order, per opened oracle, the leaf `FE-run`
//!   and its path `DIGEST`s (round 0: memory then setup).

mod decode;
mod digest;
mod gkr;
mod params;
mod replay;
mod runs;
mod whir;

use std::collections::BTreeMap;

use prover::gkr::prover::CommitmentMode;

pub use decode::{decode_structural, DecodeHints, GkrLayerHint, WhirRoundHint};
pub use digest::{digest_from_wire, digest_wire};
pub use gkr::{eval_quadratic, join_round, round_constant, split_round};
pub use params::FormatParams;

pub use replay::{replay_gkr_points, GkrReplay, LayerPoints};
pub use runs::{fe_run_len, read_fe_run, read_ts_run, ts_run_len, write_fe_run, write_ts_run};

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
pub fn check_profile(
    circuit: &Circuit,
    proof: &Proof,
    aux: &CommitmentMode,
    params: &FormatParams,
) {
    let CommitmentMode::MergedAndPackedMemoryAndWitness { pack_log2, .. } = aux else {
        panic!("expected packed commitment mode");
    };
    assert_eq!(
        circuit.trace_len,
        1 << params.trace_log2,
        "profile trace log differs from the circuit"
    );
    assert_eq!(
        *pack_log2, params.pack_log2,
        "profile packing differs from the proof aux"
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
        ws.whir_steps_schedule, params.folds,
        "profile folds differ from the proof"
    );
    assert_eq!(
        ws.whir_queries_schedule, params.queries,
        "profile queries differ from the proof"
    );
    assert_eq!(
        ws.cap_size,
        params.cap(),
        "profile cap differs from the proof"
    );
}

/// The F1 single-tx calldata of `proof`. Panics when the proof does not fit `params`, when a
/// round polynomial is not `e_z(X)` times a quadratic, or when the transcript replay misses the
/// proof's recorded handoff seed.
pub fn encode_single_tx(
    circuit: &Circuit,
    proof: &Proof,
    aux: &CommitmentMode,
    params: &FormatParams,
) -> SingleTxCalldata {
    check_profile(circuit, proof, aux, params);
    let replay = replay_gkr_points(circuit, proof, aux);
    assert_eq!(
        Some(replay.handoff_seed),
        proof.intermediate_transcript_seed,
        "GKR transcript replay diverged from the proof's handoff seed"
    );
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
