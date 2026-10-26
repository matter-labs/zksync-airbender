//! Proof → calldata flattening for the merged on-chain `GkrWhirVerifier` (one transaction:
//! the GKR stream immediately followed by the WHIR proof stream — see [`merged_calldata`]).
//!
//! All bytes are computed purely from the circuit artifact, the proof, and the aux
//! commitment-mode data — nothing here reads a fixture. The serialization mirrors
//! the reference assembler in `prover/src/tests/gkr/large_field.rs`.

use field::{Field, Proth120};
use prover::gkr::prover::OperationMode;

use crate::seed::{Circuit, Proof};

/// Serialize a Proth120 element as its 16-byte big-endian u128.
fn be16(e: Proth120) -> [u8; 16] {
    e.to_u128().to_be_bytes()
}

/// Serialize a Keccak digest (`[u32; 8]`) as 32 big-endian bytes.
fn dig32(d: &[u32; 8]) -> [u8; 32] {
    let mut o = [0u8; 32];
    for i in 0..8 {
        o[4 * i..4 * i + 4].copy_from_slice(&d[i].to_be_bytes());
    }
    o
}

/// GKR-entry output evaluations: each output type's `[evals_0, evals_1]` flattened,
/// every element as its 16-byte big-endian u128.
fn output_evals_blob(proof: &Proof) -> Vec<u8> {
    let mut blob = Vec::new();
    for v in proof.final_explicit_evaluations.values() {
        for e in v[0].iter().chain(v[1].iter()) {
            blob.extend_from_slice(&be16(*e));
        }
    }
    blob
}

/// Dimension-reducing proof data (layers with fewer sumcheck rounds than the trace's
/// variable count, processed output->base): per layer, the folding-round coefficients then
/// the final-step LSB lines (one per GKR output), all elements big-endian 16-byte.
fn dim_reduce_blob(circuit: &Circuit, proof: &Proof) -> Vec<u8> {
    let mut blob = Vec::new();
    let trace_rounds = circuit.trace_len.trailing_zeros() as usize;
    let dim_layers: Vec<usize> = proof
        .sumcheck_intermediate_values
        .keys()
        .copied()
        .filter(|l| proof.sumcheck_intermediate_values[l].sumcheck_num_rounds < trace_rounds)
        .collect();
    for &layer in dim_layers.iter().rev() {
        let siv = &proof.sumcheck_intermediate_values[&layer];
        for c in siv.internal_round_coefficients.iter() {
            for e in c.as_multilinear().iter() {
                blob.extend_from_slice(&be16(*e));
            }
        }
        for v in siv.final_step_evaluations.values() {
            blob.extend_from_slice(&be16(v[0]));
            blob.extend_from_slice(&be16(v[1]));
        }
    }
    blob
}

/// Standard circuit-layer proof data (config_idx `num_standard_layers-1 .. 0`): per
/// layer, the trace_log2 folding-round coefficients then the at-point evals in group-offset
/// order. Cached / virtual-setup inputs are computed on the verifier heap and are
/// NOT part of the calldata.
fn circuit_blob(circuit: &Circuit, proof: &Proof) -> Vec<u8> {
    use cs::definitions::GKRAddress;
    let mut blob = Vec::new();
    let num_standard_layers = circuit.layers.len();
    let num_mem = circuit.memory_layout.total_width;
    let num_wit = circuit.witness_layout.total_width;
    for config_idx in (0..num_standard_layers).rev() {
        let siv = &proof.sumcheck_intermediate_values[&config_idx];
        for c in siv.internal_round_coefficients.iter() {
            for e in c.as_multilinear().iter() {
                blob.extend_from_slice(&be16(*e));
            }
        }
        let group_idx = |addr: &GKRAddress| -> Option<usize> {
            match addr {
                GKRAddress::InnerLayer { layer, offset }
                    if *layer == config_idx && config_idx > 0 =>
                {
                    Some(*offset)
                }
                GKRAddress::BaseLayerMemory(o) if config_idx == 0 => Some(*o),
                GKRAddress::BaseLayerWitness(o) if config_idx == 0 => Some(num_mem + *o),
                GKRAddress::Setup(o) if config_idx == 0 => Some(num_mem + num_wit + *o),
                _ => None, // Cached / VirtualSetup: computed on heap, not in calldata
            }
        };
        let mut by_idx: std::collections::BTreeMap<usize, Proth120> = Default::default();
        for (addr, val) in siv.final_step_evaluations.iter() {
            if let Some(idx) = group_idx(addr) {
                by_idx.insert(idx, val[0]);
            }
        }
        for (addr, val) in siv.extra_evaluations_from_caching_relations.iter() {
            if let Some(idx) = group_idx(addr) {
                by_idx.insert(idx, *val);
            }
        }
        let n = by_idx.keys().max().map(|m| m + 1).unwrap_or(0);
        for i in 0..n {
            let v = by_idx.get(&i).copied().unwrap_or(Proth120::ZERO);
            blob.extend_from_slice(&be16(v));
        }
    }
    blob
}

/// Assemble the full GKR-verifier calldata (gkr.sol stream order):
///   preimage ‖ external-challenge PoW nonce (BE8) ‖ output-evals ‖ dim-reduce blob
///   ‖ circuit-layer blob ‖ WHIR-batching PoW nonce (BE8).
pub fn gkr_calldata(circuit: &Circuit, proof: &Proof, aux: &OperationMode) -> Vec<u8> {
    let mut cd: Vec<u8> = Vec::new();
    cd.extend_from_slice(&crate::seed::commit_seed_preimage(circuit, proof, aux));
    cd.extend_from_slice(&proof.lookup_challenges_pow_nonce.to_be_bytes());
    cd.extend_from_slice(&output_evals_blob(proof));
    cd.extend_from_slice(&dim_reduce_blob(circuit, proof));
    cd.extend_from_slice(&circuit_blob(circuit, proof));
    cd.extend_from_slice(&proof.whir_proof.batching_challenge_pow_nonce.to_be_bytes());
    cd
}

/// Single-transaction calldata for the merged `GkrWhirVerifier`: the GKR stream (which ends with
/// the WHIR-batching PoW nonce) immediately followed by the WHIR proof stream. The WHIR start
/// state (seed, batching, opening, evaluation point, base caps) is handed over in memory inside
/// the contract, so no WHIR preimage is serialized.
///
/// `folds` / `queries` are the WHIR round schedule (`whir_steps_schedule` /
/// `whir_queries_schedule` from the same `WhirSchedule` the proof was produced with and the
/// verifier is generated from), so the calldata stream matches both the prover and the verifier.
pub fn merged_calldata(
    circuit: &Circuit,
    proof: &Proof,
    aux: &OperationMode,
    folds: &[usize],
    queries: &[usize],
) -> Vec<u8> {
    let mut cd = gkr_calldata(circuit, proof, aux);
    cd.extend_from_slice(&whir_stream(circuit, proof, aux, folds, queries));
    cd
}

/// The WHIR proof stream (per round: sumcheck polys, intermediate oracle cap, ood sample, PoW
/// nonce, query openings; final round: monomials, PoW nonce, final query openings). It follows
/// the GKR stream in the merged single-transaction calldata.
pub fn whir_stream(
    _circuit: &Circuit,
    proof: &Proof,
    _aux: &OperationMode,
    folds: &[usize],
    queries: &[usize],
) -> Vec<u8> {
    assert_eq!(
        folds.len(),
        queries.len(),
        "WHIR folds/queries schedule length mismatch"
    );
    let wp = &proof.whir_proof;
    let num_rounds = folds.len();
    let mut cd: Vec<u8> = vec![];

    // ---- proof stream ----
    let push_leaf = |cd: &mut Vec<u8>, vals: &[Proth120], path: &[[u32; 8]]| {
        for v in vals.iter() {
            cd.extend_from_slice(&be16(*v));
        }
        for d in path.iter() {
            cd.extend_from_slice(&dig32(d));
        }
    };
    let push_base = |cd: &mut Vec<u8>, vals: &[Proth120], path: &[[u32; 8]], nc: usize| {
        let vp = vals.len() / nc;
        for c in 0..nc {
            for o in 0..vp {
                cd.extend_from_slice(&be16(vals[o * nc + c]));
            }
        }
        for d in path.iter() {
            cd.extend_from_slice(&dig32(d));
        }
    };
    let round_sumcheck_polys = |r: usize| -> &[[Proth120; 3]] {
        if r == 0 {
            &wp.base_sumcheck_polys
        } else {
            &wp.intermediate_whir_oracles[r - 1].sumcheck_polys
        }
    };
    let round_queries_pow_nonce = |r: usize| -> u64 {
        if r == 0 {
            wp.base_queries_pow_nonce
        } else {
            wp.intermediate_whir_oracles[r - 1].queries_pow_nonce
        }
    };
    for r in 0..num_rounds {
        assert_eq!(round_sumcheck_polys(r).len(), folds[r]);
        for sp in round_sumcheck_polys(r).iter() {
            cd.extend_from_slice(&be16(sp[0]));
            cd.extend_from_slice(&be16(sp[1]));
            cd.extend_from_slice(&be16(sp[2]));
        }
        if r < num_rounds - 1 {
            for d in wp.intermediate_whir_oracles[r].commitment.cap.cap.iter() {
                cd.extend_from_slice(&dig32(d));
            }
            let ood = &wp.intermediate_whir_oracles[r].ood_samples;
            assert_eq!(ood.len(), 1, "whir.sol takes one OOD sample per oracle");
            cd.extend_from_slice(&be16(ood[0]));
            cd.extend_from_slice(&round_queries_pow_nonce(r).to_be_bytes());
            for qq in 0..queries[r] {
                if r == 0 {
                    let mq = &wp.memory_commitment.queries[qq];
                    push_base(
                        &mut cd,
                        &mq.leaf_values_concatenated,
                        &mq.path,
                        wp.memory_commitment.num_columns,
                    );
                    let sq = &wp.setup_commitment.queries[qq];
                    push_base(
                        &mut cd,
                        &sq.leaf_values_concatenated,
                        &sq.path,
                        wp.setup_commitment.num_columns,
                    );
                } else {
                    let q = &wp.intermediate_whir_oracles[r - 1].queries[qq];
                    push_leaf(&mut cd, &q.leaf_values_concatenated, &q.path);
                }
            }
        } else {
            for m in wp.final_monomials.iter() {
                cd.extend_from_slice(&be16(*m));
            }
            cd.extend_from_slice(&round_queries_pow_nonce(r).to_be_bytes());
            for qq in 0..queries[r] {
                let q = &wp.intermediate_whir_oracles[num_rounds - 2].queries[qq];
                push_leaf(&mut cd, &q.leaf_values_concatenated, &q.path);
            }
        }
    }
    cd
}
