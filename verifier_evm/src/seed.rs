//! Commit-seed + GKR→WHIR handoff-seed reconstruction, and the registry-mark words.
//!
//! These reproduce the transcript preimage and the intermediate seeds that the
//! prover derives while emitting proof calldata, plus the `(publicInput, auxInput)` tuple
//! the on-chain verifier reports to its registry. Nothing here reads
//! a fixture; the bytes are computed purely from the circuit artifact, the proof, and the aux
//! operation mode. The calldata encoder's replay checks the reconstructed batching challenge
//! against the first WHIR sumcheck claim.

use field::Proth120;
use prover::gkr::prover::utils::flatten_merkle_caps_iter_into;
use prover::gkr::prover::{GKRProof, OperationMode};
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;

use cs::gkr_compiler::GKRCircuitArtifact;

/// The concrete Proth120 GKR circuit artifact type.
pub type Circuit = GKRCircuitArtifact<Proth120>;
/// The concrete Proth120 GKR proof type (Keccak Merkle trees).
pub type Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

/// Rebuild the transcript-init input as a `Vec<u32>` (the LE-u32 words the prover
/// keccaks into the initial seed):
///   register final states (value, ts_low, ts_high) x32, then
///   (final_pc, final_ts_low, final_ts_high), then delegation/circuit top bits,
///   then the setup-commitment cap, then the merged memory+witness cap.
pub(crate) fn build_transcript_input(proof: &Proof, aux: &OperationMode) -> Vec<u32> {
    use cs::definitions::split_timestamp;

    let OperationMode::SingleChunk {
        register_final_state,
        final_pc,
        final_timestamp,
        ..
    } = aux
    else {
        panic!("aux data must be OperationMode::SingleChunk");
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
pub fn commit_seed_preimage(_circuit: &Circuit, proof: &Proof, aux: &OperationMode) -> Vec<u8> {
    let ti = build_transcript_input(proof, aux);
    ti.iter().flat_map(|w| w.to_le_bytes()).collect()
}

/// The `(publicInput, auxInput)` tuple the on-chain verifier reports to its
/// registry (`IVerificationRegistry.markVerified`) for this proof, each as a bytes32:
///  * `public_input` = final registers x10..x17, `aux_input` = x18..x25 — each register's
///    u32 value as 4 LE bytes, concatenated in register order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedMark {
    pub public_input: [u8; 32],
    pub aux_input: [u8; 32],
}

impl VerifiedMark {
    /// The 64-byte ABI encoding `publicInput ‖ auxInput` (also what the
    /// verifier returns on success).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(64);
        v.extend_from_slice(&self.public_input);
        v.extend_from_slice(&self.aux_input);
        v
    }
}

/// Compute the registry mark for `aux` (see [`VerifiedMark`]).
pub fn verified_mark(aux: &OperationMode) -> VerifiedMark {
    let OperationMode::SingleChunk {
        register_final_state,
        ..
    } = aux
    else {
        panic!("aux data must be OperationMode::SingleChunk");
    };
    let regs = |first: usize| -> [u8; 32] {
        let mut w = [0u8; 32];
        for i in 0..8 {
            w[4 * i..4 * i + 4]
                .copy_from_slice(&register_final_state[first + i].value.to_le_bytes());
        }
        w
    };
    VerifiedMark {
        public_input: regs(10),
        aux_input: regs(18),
    }
}
