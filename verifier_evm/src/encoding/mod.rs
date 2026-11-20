//! The compressed calldata of the single-transaction L1 wrap verifier, with
//! transcript-preserving compression. The verifier reconstructs omitted values
//! before absorbing them. See `verifier_evm/gkr_transcript_reference.md`
//! for encoding invariants and verification/producer pointers.
//!
//! The calldata holds the GKR section, then the WHIR section. Registers are LE u32;
//! PoW nonces are BE u64. Field runs pack canonical 123-bit values MSB-first and
//! timestamp runs pack 19-bit limb pairs; digests use the 25-byte prefix of their
//! big-endian words. The final PC, the inits/teardowns top bits and the setup cap
//! are deployment constants.
//!
//! GKR sumcheck rounds are factored: each round polynomial is `p = e_z·u`, with
//! `e_z(X) = (1 − z) + (2z − 1)·X` and the quadratic `u = a + bX + cX²`. Only `(b, c)`
//! is sent; the verifier derives `a` from the running claim and absorbs the rebuilt
//! coefficients of `p`. A WHIR sumcheck round sends `(c0, c2)`: `c1` is derived as
//! `claim − 2·c0 − c2`. Each WHIR round's packed coefficient run is followed by
//! its folding-PoW nonce array when gated. Each intermediate cap is followed by
//! an OOD-PoW nonce when gated and one raw BE u128 OOD value.

mod digest;
mod gkr;
pub(crate) mod params;
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

/// The compressed single-tx calldata and the `(offset, length)` of every named field.
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
    let whir = &proof.whir_proof;
    let pack = 1 << params.pack_log2;
    let packed_memory =
        (circuit.memory_layout.total_width + circuit.witness_layout.total_width).div_ceil(pack);
    let packed_setup = circuit.generic_lookup_tables_width.div_ceil(pack);
    let query_shape = |round: usize, columns: usize| {
        let query_bits = params.oracles[round].query_index_bits;
        (
            1usize << query_bits,
            query_bits - params.cap_log2,
            columns << params.folds[round],
        )
    };
    let check_query = |round: usize, columns: usize, index, depth, values| {
        let (leaves, expected_depth, expected_values) = query_shape(round, columns);
        assert!(
            index < leaves,
            "WHIR round {round} query index exceeds its oracle"
        );
        assert_eq!(depth, expected_depth, "WHIR round {round} query path depth");
        assert_eq!(
            values, expected_values,
            "WHIR round {round} query leaf width"
        );
    };
    for (oracle, columns) in [
        (&whir.memory_commitment, packed_memory),
        (&whir.setup_commitment, packed_setup),
    ] {
        assert_eq!(oracle.num_columns, columns, "WHIR packed base columns");
        assert_eq!(oracle.evals.len(), columns, "WHIR packed claim count");
        assert_eq!(
            oracle.commitment.cap.cap.len(),
            params.cap(),
            "WHIR base cap size"
        );
        assert_eq!(
            oracle.queries.len(),
            params.queries[0],
            "WHIR base query count"
        );
        for q in &oracle.queries {
            check_query(
                0,
                columns,
                q.index,
                q.path.len(),
                q.leaf_values_concatenated.len(),
            );
        }
    }
    assert!(
        whir.witness_commitment.queries.is_empty(),
        "expected a merged memory and witness tree"
    );
    assert_eq!(
        whir.intermediate_whir_oracles.len(),
        params.folds.len() - 1,
        "WHIR intermediate oracle count"
    );
    for (i, oracle) in whir.intermediate_whir_oracles.iter().enumerate() {
        let round = i + 1;
        assert_eq!(
            oracle.queries.len(),
            params.queries[round],
            "WHIR round {round} query count"
        );
        for q in &oracle.queries {
            check_query(
                round,
                1,
                q.index,
                q.path.len(),
                q.leaf_values_concatenated.len(),
            );
        }
    }
    let final_log = config.whir_message_size_log2() - params.folds.iter().sum::<usize>();
    assert_eq!(
        whir.final_monomials.len(),
        1 << final_log,
        "WHIR final monomial count"
    );
}

/// The compressed single-tx calldata of `proof`. Panics when the proof does not fit `params`,
/// when a round polynomial is not `e_z(X)` times a quadratic, or when the reconstructed
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
