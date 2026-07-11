// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// Third contract linking the two independent verifiers. The GKR verifier and the
/// WHIR verifier each run in their OWN transaction with their OWN calldata, and each
/// computes the shared "committed state" (a bytes32 = keccak of the transcript state
/// at the GKR→WHIR boundary: [seed:32][batching:16][opening:16][z_initial:nz*16]
/// [witness_cap:CAP*32][setup_cap:CAP*32]). Each verifier calls its mark_* function
/// here with that commitment. A consistent proof pair emits two events carrying the
/// SAME bytes32 — that agreement is the cross-check the test asserts.
contract GkrWhirRegistry {
    event GkrVerified(bytes32 indexed commitment);
    event WhirVerified(bytes32 indexed commitment);

    /// Called by the GKR verifier with the committed state WHIR must start from.
    function mark_gkr_verified(bytes32 commitment) external {
        emit GkrVerified(commitment);
    }

    /// Called by the WHIR verifier with the committed state it recomputed itself
    /// (keccak of its own transcript-state calldata — not a checked preimage).
    function mark_whir_verified(bytes32 commitment) external {
        emit WhirVerified(commitment);
    }
}
