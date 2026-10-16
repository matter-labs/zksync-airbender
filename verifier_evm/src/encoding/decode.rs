//! Structural F1 → v0 decoder: rebuilds the v0 GKR calldata and the v0 WHIR proof stream
//! (without its committed-state header) from F1 bytes and the values F1 omits or the
//! verifier derives. A test oracle for the encoder; the generated verifier is the consumer.

use field::{Field, Proth120};
use prover::gkr::prover::CommitmentMode;

use super::digest::digest_from_wire;
use super::gkr::{eval_quadratic, join_round, round_constant};
use super::params::FormatParams;
use super::replay::{dim_reducing_layers, replay_gkr_points};
use super::runs::{fe_run_len, read_fe_run, read_ts_run, ts_run_len};
use crate::seed::{Circuit, Proof};

/// One GKR sumcheck layer in processing order.
#[derive(Clone, Debug)]
pub struct GkrLayerHint {
    /// Round `i` binds against `z[i]` and draws `r[i]` (transcript replay).
    pub z: Vec<Proth120>,
    pub r: Vec<Proth120>,
    /// The layer's initial claim (`K` at round 0).
    pub entry_claim: Proth120,
    /// Elements after the rounds: LSB lines or at-point evals.
    pub evals: usize,
}

#[derive(Clone, Debug)]
pub struct WhirRoundHint {
    /// The running claim before each sumcheck step (E2).
    pub step_claims: Vec<Proth120>,
    /// Final-polynomial monomials (final round only).
    pub monomials: usize,
    /// Per opened oracle of a query: (leaf values, path digests); round 0 opens memory then setup.
    pub oracles: Vec<(usize, usize)>,
}

/// Deployment constants and verifier-derived values the decoder needs.
#[derive(Clone, Debug)]
pub struct DecodeHints {
    pub final_pc: u32,
    pub setup_cap: Vec<[u32; 8]>,
    pub num_registers: usize,
    pub num_top_bits: usize,
    pub output_evals: usize,
    pub gkr_layers: Vec<GkrLayerHint>,
    pub whir_rounds: Vec<WhirRoundHint>,
    /// Per round-0 query, the setup-path siblings above the setup frontier, derived from the
    /// pinned frontier and the query's physical index (the verifier's view of them).
    pub setup_path_tails: Vec<Vec<[u32; 8]>>,
}

fn sum(els: &[Proth120]) -> Proth120 {
    els.iter().fold(Proth120::ZERO, |mut acc, e| {
        acc.add_assign(e);
        acc
    })
}

impl DecodeHints {
    /// `setup_frontier`: the pinned setup-tree nodes at `params.setup_frontier_level` (physical
    /// order), required when that level lies below the cap.
    pub fn from_proof(
        circuit: &Circuit,
        proof: &Proof,
        aux: &CommitmentMode,
        params: &FormatParams,
        setup_frontier: Option<&[[u32; 8]]>,
    ) -> Self {
        let CommitmentMode::MergedAndPackedMemoryAndWitness {
            final_pc,
            register_final_state,
            ..
        } = aux
        else {
            panic!("expected packed commitment mode");
        };
        let replay = replay_gkr_points(circuit, proof, aux);
        let layer_order: Vec<usize> = dim_reducing_layers(circuit, proof)
            .into_iter()
            .chain((0..circuit.layers.len()).rev())
            .collect();
        let gkr_layers = replay
            .layers
            .iter()
            .zip(layer_order)
            .map(|(lp, layer)| {
                assert_eq!(lp.layer, layer);
                let siv = &proof.sumcheck_intermediate_values[&layer];
                let c = siv.internal_round_coefficients[0].as_multilinear();
                let evals = if layer >= circuit.layers.len() {
                    2 * siv.final_step_evaluations.len()
                } else {
                    crate::flatten::circuit_layer_evals(circuit, proof, layer).len()
                };
                GkrLayerHint {
                    z: lp.z.clone(),
                    r: lp.r.clone(),
                    entry_claim: sum(&[c[0], c[0], c[1], c[2], c[3]]),
                    evals,
                }
            })
            .collect();

        let wp = &proof.whir_proof;
        let num_rounds = params.folds.len();
        let shape = |mut sizes: Vec<(usize, usize)>| {
            sizes.dedup();
            assert_eq!(sizes.len(), 1, "queries of one oracle differ in shape");
            sizes[0]
        };
        let mut steps = wp.sumcheck_polys.iter();
        let whir_rounds = (0..num_rounds)
            .map(|r| WhirRoundHint {
                step_claims: (0..params.folds[r])
                    .map(|_| {
                        let sp = steps.next().unwrap();
                        sum(&[sp[0], sp[0], sp[1], sp[2]])
                    })
                    .collect(),
                monomials: if r == num_rounds - 1 {
                    wp.final_monomials.len()
                } else {
                    0
                },
                oracles: if r == 0 {
                    vec![
                        shape(
                            wp.memory_commitment
                                .queries
                                .iter()
                                .map(|q| (q.leaf_values_concatenated.len(), q.path.len()))
                                .collect(),
                        ),
                        shape(
                            wp.setup_commitment
                                .queries
                                .iter()
                                .map(|q| {
                                    (
                                        q.leaf_values_concatenated.len(),
                                        q.path.len() - params.setup_frontier_skip(),
                                    )
                                })
                                .collect(),
                        ),
                    ]
                } else {
                    vec![shape(
                        wp.intermediate_whir_oracles[r - 1]
                            .queries
                            .iter()
                            .map(|q| (q.leaf_values_concatenated.len(), q.path.len()))
                            .collect(),
                    )]
                },
            })
            .collect();
        Self {
            final_pc: *final_pc,
            setup_cap: wp.setup_commitment.commitment.cap.cap.clone(),
            num_registers: register_final_state.len(),
            num_top_bits: proof.inits_and_teardowns_top_bits.len(),
            output_evals: proof
                .final_explicit_evaluations
                .values()
                .map(|v| v[0].len() + v[1].len())
                .sum(),
            gkr_layers,
            whir_rounds,
            setup_path_tails: setup_path_tails(proof, params, setup_frontier),
        }
    }
}

/// The setup-path siblings above the frontier of every round-0 query: the sibling `j` levels
/// above the frontier is node `(i >> j) ^ 1` of the frontier reduced `j` levels, `i` the query's
/// frontier index.
fn setup_path_tails(
    proof: &Proof,
    params: &FormatParams,
    setup_frontier: Option<&[[u32; 8]]>,
) -> Vec<Vec<[u32; 8]>> {
    let skip = params.setup_frontier_skip();
    let queries = &proof.whir_proof.setup_commitment.queries;
    if skip == 0 {
        return vec![Vec::new(); queries.len()];
    }
    let frontier = setup_frontier.expect("a setup frontier below the cap needs its nodes");
    assert_eq!(frontier.len(), 1 << params.setup_frontier_level);
    let levels: Vec<Vec<[u32; 8]>> = (0..skip)
        .map(|j| super::digest::merkle_reduce(frontier, j, params.digest_bytes))
        .collect();
    queries
        .iter()
        .map(|q| {
            let height = q.path.len() - skip;
            let i = q.index >> height;
            (0..skip).map(|j| levels[j][(i >> j) ^ 1]).collect()
        })
        .collect()
}

struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> &'a [u8] {
        assert!(self.pos + n <= self.bytes.len(), "F1 stream truncated");
        let out = &self.bytes[self.pos..self.pos + n];
        self.pos += n;
        out
    }

    fn fe_run(&mut self, n: usize) -> Vec<Proth120> {
        read_fe_run(self.take(fe_run_len(n)), n)
    }

    fn digests(&mut self, n: usize, digest_bytes: usize) -> Vec<[u32; 8]> {
        (0..n)
            .map(|_| digest_from_wire(self.take(digest_bytes)))
            .collect()
    }
}

fn be16(out: &mut Vec<u8>, els: &[Proth120]) {
    for e in els {
        out.extend_from_slice(&e.to_u128().to_be_bytes());
    }
}

fn be_digests(out: &mut Vec<u8>, ds: &[[u32; 8]]) {
    for d in ds {
        for w in d {
            out.extend_from_slice(&w.to_be_bytes());
        }
    }
}

fn le_words(out: &mut Vec<u8>, words: impl IntoIterator<Item = u32>) {
    for w in words {
        out.extend_from_slice(&w.to_le_bytes());
    }
}

/// Decodes the single-tx F1 stream into `(gkr_v0, whir_v0_stream)`; panics on any malformed
/// or trailing byte.
pub fn decode_structural(
    bytes: &[u8],
    params: &FormatParams,
    hints: &DecodeHints,
) -> (Vec<u8>, Vec<u8>) {
    let mut rd = Reader { bytes, pos: 0 };
    let cap = params.cap();

    let mut gkr = Vec::new();
    let registers: Vec<u32> = rd
        .take(4 * hints.num_registers)
        .as_chunks::<4>()
        .0
        .iter()
        .map(|w| u32::from_le_bytes(*w))
        .collect();
    let timestamps = read_ts_run(
        rd.take(ts_run_len(hints.num_registers + 1)),
        hints.num_registers + 1,
    );
    for (value, (lo, hi)) in registers.iter().zip(&timestamps) {
        le_words(&mut gkr, [*value, *lo, *hi]);
    }
    let (final_lo, final_hi) = timestamps[hints.num_registers];
    le_words(&mut gkr, [hints.final_pc, final_lo, final_hi]);
    let top_bits = rd.take(4 * hints.num_top_bits).to_vec();
    gkr.extend_from_slice(&top_bits);
    le_words(&mut gkr, hints.setup_cap.iter().flatten().copied());
    let memory_cap = rd.digests(cap, params.digest_bytes);
    le_words(&mut gkr, memory_cap.iter().flatten().copied());
    gkr.extend_from_slice(rd.take(8)); // external PoW nonce
    be16(&mut gkr, &rd.fe_run(hints.output_evals));
    for layer in hints.gkr_layers.iter() {
        let bc = rd.fe_run(2 * layer.z.len());
        let mut k = layer.entry_claim;
        for ((pair, z), r) in bc.as_chunks::<2>().0.iter().zip(&layer.z).zip(&layer.r) {
            let u = [round_constant(k, *z, pair[0], pair[1]), pair[0], pair[1]];
            be16(&mut gkr, &join_round(u, *z));
            k = eval_quadratic(u, *r);
        }
        be16(&mut gkr, &rd.fe_run(layer.evals));
    }
    gkr.extend_from_slice(rd.take(8)); // WHIR batching PoW nonce

    let mut whir = Vec::new();
    let num_rounds = hints.whir_rounds.len();
    for (r, round) in hints.whir_rounds.iter().enumerate() {
        let c0c2 = rd.fe_run(2 * round.step_claims.len());
        for (pair, claim) in c0c2.as_chunks::<2>().0.iter().zip(&round.step_claims) {
            let mut c1 = *claim;
            c1.sub_assign(&pair[0]);
            c1.sub_assign(&pair[0]);
            c1.sub_assign(&pair[1]);
            be16(&mut whir, &[pair[0], c1, pair[1]]);
        }
        if r < num_rounds - 1 {
            be_digests(&mut whir, &rd.digests(cap, params.digest_bytes));
            let ood = rd.take(16);
            assert!(
                u128::from_be_bytes(ood.try_into().unwrap()) < Proth120::ORDER,
                "non-canonical field element"
            );
            whir.extend_from_slice(ood);
        } else {
            be16(&mut whir, &rd.fe_run(round.monomials));
        }
        whir.extend_from_slice(rd.take(8)); // PoW nonce
        for q in 0..params.queries[r] {
            for (o, (values, path)) in round.oracles.iter().enumerate() {
                be16(&mut whir, &rd.fe_run(*values));
                be_digests(&mut whir, &rd.digests(*path, params.digest_bytes));
                // round 0's second oracle is the setup tree, whose path stops at the frontier
                if r == 0 && o == 1 {
                    be_digests(&mut whir, &hints.setup_path_tails[q]);
                }
            }
        }
    }
    assert_eq!(rd.pos, bytes.len(), "trailing bytes after the F1 stream");
    (gkr, whir)
}
