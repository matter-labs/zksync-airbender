//! Commit-seed + GKR→WHIR handoff-seed reconstruction.
//!
//! These reproduce the transcript preimage and the intermediate seeds that the
//! prover derives while emitting proof calldata. Nothing here reads a fixture; the
//! bytes are computed purely from the circuit artifact, the proof, and the aux
//! commitment-mode data. The logic mirrors the reference simulation in
//! `prover/src/tests/gkr/large_field.rs::verify_dim_reduce_layers`.

use field::Proth120;
use prover::gkr::prover::transcript_utils::{
    commit_field_els, draw_random_field_els, draw_random_field_els_with_pow,
};
use prover::gkr::prover::utils::flatten_merkle_caps_iter_into;
use prover::gkr::prover::{CommitmentMode, GKRProof};
use prover::gkr::prover_config::pow_bits;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use transcript::{Keccak256Transcript, Transcript};
use worker::Worker;

use cs::gkr_compiler::GKRCircuitArtifact;

/// The concrete Proth120 GKR circuit artifact type.
pub type Circuit = GKRCircuitArtifact<Proth120>;
/// The concrete Proth120 GKR proof type (Keccak Merkle trees).
pub type Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

/// `pack_log2` baked into the Proth120 EVM-production proof.
const PACK_LOG2: usize = 4;
/// `base_lde_factor = 1 << 5` for the Proth120 EVM WHIR schedule.
const BASE_LDE_FACTOR: usize = 5;

/// Extract `external_challenges_pow_bits` from the aux commitment-mode data.
fn external_pow_bits(aux: &CommitmentMode) -> u32 {
    match aux {
        CommitmentMode::MergedAndPackedMemoryAndWitness {
            external_challenges_pow_bits,
            ..
        } => *external_challenges_pow_bits,
        _ => panic!("aux data must be MergedAndPackedMemoryAndWitness"),
    }
}

/// Rebuild the transcript-init input as a `Vec<u32>` (the LE-u32 words the prover
/// keccaks into the initial seed):
///   register final states (value, ts_low, ts_high) x32, then
///   (final_pc, final_ts_low, final_ts_high), then delegation/circuit top bits,
///   then the setup-commitment cap, then the merged memory+witness cap.
pub(crate) fn build_transcript_input(proof: &Proof, aux: &CommitmentMode) -> Vec<u32> {
    use cs::definitions::split_timestamp;

    let CommitmentMode::MergedAndPackedMemoryAndWitness {
        register_final_state,
        final_pc,
        final_timestamp,
        ..
    } = aux
    else {
        panic!("aux data must be MergedAndPackedMemoryAndWitness");
    };

    let mut ti: Vec<u32> = Vec::new();
    for reg in register_final_state.iter() {
        let (ts_low, ts_high) = split_timestamp(reg.last_access_timestamp);
        ti.push(reg.value);
        ti.push(ts_low);
        ti.push(ts_high);
    }
    let (final_ts_low, final_ts_high) = split_timestamp(*final_timestamp);
    ti.push(*final_pc);
    ti.push(final_ts_low);
    ti.push(final_ts_high);

    ti.extend_from_slice(&proof.inits_and_teardowns_top_bits[..]);
    flatten_merkle_caps_iter_into(
        Some(proof.whir_proof.setup_commitment.commitment.cap.clone()).into_iter(),
        &mut ti,
    );
    flatten_merkle_caps_iter_into(
        Some(proof.whir_proof.memory_commitment.commitment.cap.clone()).into_iter(),
        &mut ti,
    );
    ti
}

/// The transcript preimage (little-endian bytes of the u32 words) whose keccak256
/// is the initial GKR verifier seed.
pub fn commit_seed_preimage(_circuit: &Circuit, proof: &Proof, aux: &CommitmentMode) -> Vec<u8> {
    let ti = build_transcript_input(proof, aux);
    ti.iter().flat_map(|w| w.to_le_bytes()).collect()
}

/// The transcript state at the GKR→WHIR handoff, and the derived WHIR opening data
/// (only computed when `want_opening` is set).
pub struct HandoffState {
    pub seed: [u8; 32],
    pub whir_batching: Proth120,
    pub batched_opening: Proth120,
    pub whir_point: Vec<Proth120>,
}

/// Re-derive the full GKR→WHIR handoff state (seed + batching + opening + evaluation point) by
/// replaying the GKR transcript. Kept for the one-time proof migration that backfills the
/// `WhirPolyCommitProof` handoff fields into older proof jsons (and as an independent check).
pub fn replay_handoff_state(
    circuit: &Circuit,
    proof: &Proof,
    aux: &CommitmentMode,
) -> HandoffState {
    replay_handoff(circuit, proof, aux, true)
}

/// Replay the full GKR verifier transcript (STEP 1 external challenges, STEP 2a GKR
/// entry, the dimension-reducing layers, the standard circuit layers, and the STEP 4
/// packed-commitment handoff) purely for its seed-affecting `commit`/`draw` calls,
/// returning the state at the WHIR handoff. Field arithmetic (merge / batched
/// opening) is only performed when `want_opening` is true.
pub(crate) fn replay_handoff(
    circuit: &Circuit,
    proof: &Proof,
    aux: &CommitmentMode,
    want_opening: bool,
) -> HandoffState {
    use field::Field;

    type E = Proth120;
    let worker = Worker::new_with_num_threads(4);

    let ti = build_transcript_input(proof, aux);
    let mut seed = <Keccak256Transcript as Transcript<Proth120, Proth120>>::commit_initial_u32(&ti);

    // ---- STEP 1: external challenges (PoW-gated draw of 9 elements) ----
    let entry_pow = core::cmp::max(
        pow_bits::lookup_challenges_pow_bits(
            prover::definitions::SecurityLevel::Sec100.security_bits(),
            pow_bits::lookup_identity_degree(circuit),
        ),
        external_pow_bits(aux),
    );
    let _ = draw_random_field_els_with_pow::<Proth120, Proth120, Keccak256Transcript>(
        &mut seed, 9, entry_pow, &worker,
    );

    // ---- STEP 2a: absorb output evals, draw eval_point + batching ----
    let mut evals_flat: Vec<E> = vec![];
    for (_t, v) in proof.final_explicit_evaluations.iter() {
        evals_flat.extend_from_slice(&v[0]);
        evals_flat.extend_from_slice(&v[1]);
    }
    commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &evals_flat);
    let final_trace_size_log_2 = proof.final_explicit_evaluations.values().next().unwrap()[0]
        .len()
        .trailing_zeros() as usize;
    let _ = draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(
        &mut seed,
        final_trace_size_log_2 + 1,
    );

    // ---- dimension-reducing layers (num_rounds < 22), processed output->base ----
    let dim_layers: Vec<usize> = proof
        .sumcheck_intermediate_values
        .keys()
        .copied()
        .filter(|l| proof.sumcheck_intermediate_values[l].sumcheck_num_rounds < 22)
        .collect();
    for &layer in dim_layers.iter().rev() {
        let siv = &proof.sumcheck_intermediate_values[&layer];
        for round in 0..siv.sumcheck_num_rounds {
            let c = siv.internal_round_coefficients[round];
            commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &c);
            let _ = draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, 1);
        }
        let lsb_flat: Vec<E> = siv
            .final_step_evaluations
            .values()
            .flat_map(|v| [v[0], v[1]])
            .collect();
        commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &lsb_flat);
        let _ = draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, 2);
    }

    // ---- standard circuit layers (config_idx num_standard_layers-1 .. 0) ----
    let num_standard_layers = circuit.layers.len();
    let mut base_layer_z: Vec<E> = vec![];
    let mut layer0_merged: std::collections::BTreeMap<cs::definitions::GKRAddress, E> =
        Default::default();
    for config_idx in (0..num_standard_layers).rev() {
        let siv = &proof.sumcheck_intermediate_values[&config_idx];
        let mut new_point: Vec<E> = Vec::with_capacity(siv.sumcheck_num_rounds);
        for round in 0..siv.sumcheck_num_rounds {
            let cflat: Vec<E> = siv.internal_round_coefficients[round].to_vec();
            commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &cflat);
            let r =
                draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, 1)[0];
            new_point.push(r);
        }
        let evals: Vec<E> = siv.final_step_evaluations.values().map(|v| v[0]).collect();
        commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &evals);
        let _ = draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, 1);
        let extra = &siv.extra_evaluations_from_caching_relations;
        if !extra.is_empty() {
            let extra_vals: Vec<E> = extra.values().copied().collect();
            commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &extra_vals);
        }
        if config_idx == 0 {
            base_layer_z = new_point;
            let mut merged: std::collections::BTreeMap<cs::definitions::GKRAddress, E> =
                Default::default();
            for (k, v) in siv.final_step_evaluations.iter() {
                merged.insert(*k, v[0]);
            }
            for (k, v) in extra.iter() {
                merged.insert(*k, *v);
            }
            layer0_merged = merged;
        }
    }

    // ---- STEP 4: packed-commitment handoff ----
    let extra =
        draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, PACK_LOG2);
    let whir_pow = pow_bits::batched_proximity_check_pow_bits(
        prover::definitions::SecurityLevel::Sec100.security_bits(),
        circuit.trace_len.trailing_zeros() as usize,
        BASE_LDE_FACTOR,
        pow_bits::total_base_oracle_columns(circuit),
    );
    let (_nonce, wbc) = draw_random_field_els_with_pow::<Proth120, Proth120, Keccak256Transcript>(
        &mut seed, 1, whir_pow, &worker,
    );
    let whir_batching = wbc[0];
    let handoff_seed = seed.0;

    // extended WHIR point = extra || base_layer_z (pack_log2 + 22 coords)
    let mut whir_point = extra.clone();
    whir_point.extend_from_slice(&base_layer_z);

    let mut batched_opening = E::ZERO;
    if want_opening {
        use cs::definitions::GKRAddress;
        let get = |addr: GKRAddress| -> E {
            *layer0_merged.get(&addr).expect("base-layer claim present")
        };
        let num_mem = circuit.memory_layout.total_width;
        let num_wit = circuit.witness_layout.total_width;
        let num_setup = circuit.generic_lookup_tables_width;
        let mut mem_wit: Vec<E> = (0..num_mem)
            .map(|i| get(GKRAddress::BaseLayerMemory(i)))
            .collect();
        mem_wit.extend((0..num_wit).map(|i| get(GKRAddress::BaseLayerWitness(i))));
        let setup_claims: Vec<E> = (0..num_setup).map(|i| get(GKRAddress::Setup(i))).collect();

        let merge = |input: &[E], extra: &[E]| -> Vec<E> {
            let pl = extra.len();
            let mut result = vec![];
            for chunk in input.chunks(1 << pl) {
                let mut v: Vec<E> = chunk.to_vec();
                v.resize(1 << pl, E::ZERO);
                for r in extra.iter().rev() {
                    let mut buf = Vec::with_capacity(v.len() / 2);
                    for pair in v.chunks(2) {
                        let mut t = pair[1];
                        t.sub_assign(&pair[0]);
                        t.mul_assign(r);
                        t.add_assign(&pair[0]);
                        buf.push(t);
                    }
                    v = buf;
                }
                result.push(v[0]);
            }
            result
        };
        let merged_mw = merge(&mem_wit, &extra);
        let merged_setup = merge(&setup_claims, &extra);

        let mut b = E::ONE;
        for c in merged_mw.iter().chain(merged_setup.iter()) {
            let mut t = b;
            t.mul_assign(c);
            batched_opening.add_assign(&t);
            b.mul_assign(&whir_batching);
        }
    }

    HandoffState {
        seed: handoff_seed,
        whir_batching,
        batched_opening,
        whir_point,
    }
}

/// The seed WHIR verification starts from — the GKR verifier's transcript state at the
/// packed-commitment handoff. Reads the value the prover stashed in the proof
/// (`intermediate_transcript_seed`); the transcript is NOT replayed here. Use
/// [`replay_handoff_seed`] to (re)derive it from scratch (e.g. the one-time proof migration).
pub fn gkr_whir_handoff_seed(proof: &Proof) -> [u8; 32] {
    proof.intermediate_transcript_seed.expect(
        "proof.intermediate_transcript_seed is not set — regenerate the proof with a prover that \
         records it, or run the `update_proof_seed` migration test on an older proof json",
    )
}

/// Re-derive the handoff seed by replaying the full GKR verifier transcript. This is the
/// "unrolled transcript reproduction" the production path avoids; kept for the one-time
/// migration that backfills `intermediate_transcript_seed` into older proof jsons, and as an
/// independent cross-check that the stored seed is correct.
pub fn replay_handoff_seed(circuit: &Circuit, proof: &Proof, aux: &CommitmentMode) -> [u8; 32] {
    replay_handoff(circuit, proof, aux, false).seed
}
