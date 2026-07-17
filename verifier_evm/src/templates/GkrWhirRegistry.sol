// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// Third contract linking the two independent verifiers. The GKR verifier and the
/// WHIR verifier each run in their OWN transaction with their OWN calldata, and each
/// computes the shared "committed state" (a bytes32 = keccak of the transcript state
/// at the GKR→WHIR boundary: [seed:32][batching:16][opening:16][z_initial:nz*16]
/// [memory_cap:CAP*32][setup_cap:CAP*32]). Each verifier calls its mark_* function
/// here with that commitment. A consistent proof pair records both bits against the
/// SAME commitment; that agreement is the cross-check.
contract GkrWhirRegistry {
    /// Which verifiers have accepted a given committed state. Modeled as a bitmask
    /// enum: GKR = bit 0, WHIR = bit 1. `Both` is the accept state for a proof pair.
    enum VerificationMask {
        None, // 0b00
        Gkr, // 0b01
        Whir, // 0b10
        Both // 0b11
    }

    /// The GKR verifier's public data bound to a commitment.
    struct PublicData {
        bytes32 public_input; // registers x10..x17 (a0..a7), each u32 as LE bytes
        bytes32 setup_commitment; // registers x18..x25 (s2..s9), each u32 as LE bytes
    }

    /// commitment => (public_input, setup_commitment), written by the GKR verifier.
    mapping(bytes32 => PublicData) public commitmentPublicData;
    /// commitment => which verifiers have accepted it (VerificationMask bits).
    mapping(bytes32 => VerificationMask) public verificationMask;

    event GkrVerified(bytes32 indexed commitment, bytes32 public_input, bytes32 setup_commitment);
    event WhirVerified(bytes32 indexed commitment);

    /// Called by the GKR verifier with the committed state WHIR must start from, plus
    /// the program's public input and setup commitment extracted from the final registers.
    function mark_gkr_verified(bytes32 commitment, bytes32 public_input, bytes32 setup_commitment) external {
        commitmentPublicData[commitment] = PublicData(public_input, setup_commitment);
        verificationMask[commitment] =
            VerificationMask(uint8(verificationMask[commitment]) | uint8(VerificationMask.Gkr));
        emit GkrVerified(commitment, public_input, setup_commitment);
    }

    /// Called by the WHIR verifier with the committed state it recomputed itself
    /// (keccak of its own transcript-state calldata — not a checked preimage).
    function mark_whir_verified(bytes32 commitment) external {
        verificationMask[commitment] =
            VerificationMask(uint8(verificationMask[commitment]) | uint8(VerificationMask.Whir));
        emit WhirVerified(commitment);
    }
}
