//! Proof → calldata flattening for the on-chain GKR and WHIR verifiers.
//!
//! All bytes are computed purely from the circuit artifact, the proof, and the aux
//! commitment-mode data — nothing here reads a fixture. The serialization mirrors
//! the reference assembler in `prover/src/tests/gkr/large_field.rs`.

use field::{Field, Proth120};
use prover::gkr::prover::CommitmentMode;

use crate::seed::{Circuit, Proof};

/// A named field's byte offset and encoded value, recorded by the serializer.
#[derive(Clone, Debug)]
pub struct CalldataField {
    pub offset: usize,
    pub value: Vec<u8>,
}

impl CalldataField {
    fn append(calldata: &mut Vec<u8>, value: &[u8]) -> Self {
        let field = Self {
            offset: calldata.len(),
            value: value.to_vec(),
        };
        calldata.extend_from_slice(value);
        field
    }
}

#[derive(Clone, Debug)]
pub struct GkrCalldataFields {
    pub final_pc: CalldataField,
    pub external_pow_nonce: CalldataField,
}

#[derive(Clone, Debug)]
pub struct WhirCalldataFields {
    pub batched_opening: CalldataField,
}

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

/// Dimension-reducing proof data (layers after the circuit's standard layers, processed
/// output->base): per layer, the folding-round coefficients then the 10 final-step
/// LSB lines, all elements big-endian 16-byte.
fn dim_reduce_blob(circuit: &Circuit, proof: &Proof) -> Vec<u8> {
    let mut blob = Vec::new();
    let dim_layers: Vec<usize> = proof
        .sumcheck_intermediate_values
        .keys()
        .copied()
        .filter(|l| *l >= circuit.layers.len())
        .collect();
    let trace_log2 = circuit.trace_len.ilog2() as usize;
    assert_eq!(
        dim_layers.len(),
        trace_log2 - crate::EXPLICIT_OUTPUT_LOG2,
        "dimension-reducing layer count must match the circuit"
    );
    for (k, &layer) in dim_layers.iter().rev().enumerate() {
        let siv = &proof.sumcheck_intermediate_values[&layer];
        assert!(
            siv.sumcheck_num_rounds < circuit.trace_len.ilog2() as usize,
            "dimension-reducing layer must have fewer rounds than the circuit"
        );
        assert_eq!(
            siv.sumcheck_num_rounds,
            crate::EXPLICIT_OUTPUT_LOG2 + k,
            "dimension-reducing rounds must increase from the explicit output"
        );
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
/// layer, the trace-log folding-round coefficients then the at-point evals in group-offset
/// order. Cached / virtual-setup inputs are computed on the verifier heap and are
/// NOT part of the calldata.
fn circuit_blob(circuit: &Circuit, proof: &Proof) -> Vec<u8> {
    use cs::definitions::GKRAddress;
    let mut blob = Vec::new();
    let num_standard_layers = circuit.layers.len();
    let num_mem = circuit.memory_layout.total_width;
    let num_wit = circuit.witness_layout.total_width;
    for config_idx in (0..num_standard_layers).rev() {
        let siv = proof
            .sumcheck_intermediate_values
            .get(&config_idx)
            .expect("proof is missing a standard circuit layer");
        assert_eq!(
            siv.sumcheck_num_rounds,
            circuit.trace_len.ilog2() as usize,
            "standard layer rounds must match the circuit"
        );
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
pub fn gkr_calldata(circuit: &Circuit, proof: &Proof, aux: &CommitmentMode) -> Vec<u8> {
    gkr_calldata_with_fields(circuit, proof, aux).0
}

/// Serialize GKR calldata and expose semantic fields for consumers such as
/// mutation tests. Offsets follow the actual preimage and shared machine ABI.
pub fn gkr_calldata_with_fields(
    circuit: &Circuit,
    proof: &Proof,
    aux: &CommitmentMode,
) -> (Vec<u8>, GkrCalldataFields) {
    let mut cd: Vec<u8> = Vec::new();
    cd.extend_from_slice(&crate::seed::commit_seed_preimage(circuit, proof, aux));
    let CommitmentMode::MergedAndPackedMemoryAndWitness { final_pc, .. } = aux else {
        panic!("expected packed commitment mode");
    };
    let final_pc = CalldataField {
        offset: crate::generator::PREIMAGE_REGISTERS_BYTES,
        value: final_pc.to_le_bytes().to_vec(),
    };
    assert_eq!(
        &cd[final_pc.offset..final_pc.offset + final_pc.value.len()],
        final_pc.value
    );
    let external_pow_nonce =
        CalldataField::append(&mut cd, &proof.lookup_challenges_pow_nonce.to_be_bytes());
    cd.extend_from_slice(&output_evals_blob(proof));
    cd.extend_from_slice(&dim_reduce_blob(circuit, proof));
    cd.extend_from_slice(&circuit_blob(circuit, proof));
    cd.extend_from_slice(&proof.batched_proximity_check_pow_nonce.to_be_bytes());
    (
        cd,
        GkrCalldataFields {
            final_pc,
            external_pow_nonce,
        },
    )
}

/// Assemble the WHIR-verifier calldata (whir.sol preimage + proof-stream layout):
///   preimage [seed:32][batching:16][opening:16][z:nz*16][witCap][setupCap]
///   then the proof stream (per WHIR round: sumcheck polys, intermediate oracle cap,
///   ood sample, PoW nonce, query openings; final round: monomials, PoW nonce,
///   final query openings).
///
/// `folds` / `queries` are the WHIR round schedule (`whir_steps_schedule` /
/// `whir_queries_schedule` from the same `WhirSchedule` the proof was produced with and the WHIR
/// verifier is generated from), so the calldata stream matches both the prover and the verifier.
///
/// Needs the circuit + aux to reconstruct the handoff seed / batching / opening /
/// evaluation point (none of which live in the proof); the proof stream itself comes
/// from `proof.whir_proof`.
pub fn whir_calldata(
    circuit: &Circuit,
    proof: &Proof,
    aux: &CommitmentMode,
    folds: &[usize],
    queries: &[usize],
) -> Vec<u8> {
    whir_calldata_with_fields(circuit, proof, aux, folds, queries).0
}

/// Serialize WHIR calldata and record the opening field as it is appended.
pub fn whir_calldata_with_fields(
    _circuit: &Circuit,
    proof: &Proof,
    _aux: &CommitmentMode,
    folds: &[usize],
    queries: &[usize],
) -> (Vec<u8>, WhirCalldataFields) {
    assert_eq!(
        folds.len(),
        queries.len(),
        "WHIR folds/queries schedule length mismatch"
    );
    // Every committed-state value now comes straight from the proof — no GKR transcript replay:
    // the seed from GKRProof.intermediate_transcript_seed, and batching / batched-opening /
    // evaluation-point from the WHIR sub-proof's handoff fields (populated by the prover).
    let wp = &proof.whir_proof;
    let handoff_seed = crate::seed::gkr_whir_handoff_seed(proof);
    let whir_batching = wp
        .batching_challenge
        .expect("whir_proof.batching_challenge not set — regenerate the proof");
    let batched_opening = wp
        .batched_opening
        .expect("whir_proof.batched_opening not set — regenerate the proof");
    let whir_point = wp
        .original_evaluation_point
        .as_ref()
        .expect("whir_proof.original_evaluation_point not set — regenerate the proof");

    let num_rounds = folds.len();

    let mut cd: Vec<u8> = vec![];
    // ---- preimage ----
    cd.extend_from_slice(&handoff_seed);
    cd.extend_from_slice(&be16(whir_batching));
    let batched_opening = CalldataField::append(&mut cd, &be16(batched_opening));
    for e in whir_point.iter() {
        cd.extend_from_slice(&be16(*e));
    }
    for d in wp.memory_commitment.commitment.cap.cap.iter() {
        cd.extend_from_slice(&dig32(d));
    }
    for d in wp.setup_commitment.commitment.cap.cap.iter() {
        cd.extend_from_slice(&dig32(d));
    }

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
    let mut sc = 0usize;
    for r in 0..num_rounds {
        for _ in 0..folds[r] {
            let sp = &wp.sumcheck_polys[sc];
            sc += 1;
            cd.extend_from_slice(&be16(sp[0]));
            cd.extend_from_slice(&be16(sp[1]));
            cd.extend_from_slice(&be16(sp[2]));
        }
        if r < num_rounds - 1 {
            for d in wp.intermediate_whir_oracles[r].commitment.cap.cap.iter() {
                cd.extend_from_slice(&dig32(d));
            }
            cd.extend_from_slice(&be16(wp.ood_samples[r]));
            cd.extend_from_slice(&wp.pow_nonces[r].to_be_bytes());
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
            cd.extend_from_slice(&wp.pow_nonces[r].to_be_bytes());
            for qq in 0..queries[r] {
                let q = &wp.intermediate_whir_oracles[num_rounds - 2].queries[qq];
                push_leaf(&mut cd, &q.leaf_values_concatenated, &q.path);
            }
        }
    }
    (cd, WhirCalldataFields { batched_opening })
}
