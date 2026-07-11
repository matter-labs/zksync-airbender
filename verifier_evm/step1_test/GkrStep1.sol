// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// STEP 1 of the production GKR verifier: the circuit-AGNOSTIC transcript
/// initialization for `CommitmentMode::MergedAndPackedMemoryAndWitness`.
///
/// This is the "written once" part (no circuit-specific gate logic). It reproduces,
/// keccak-for-keccak, the prover's Fiat-Shamir derivation of `GKRExternalChallenges`
/// + the two lookup challenges. See `verifier_evm/gkr_transcript_reference.md`.
///
///   seed      = keccak256(transcript_input)         // commit_initial_u32
///   // transcript_input = top_bits(LE u32) || setup_cap(32B*) || merged_cap(32B*)
///   seed      = keccak256(seed || be8(nonce))       // PoW fold; assert top powBits zero
///   for i in 0..9: seed = keccak256(seed); ch[i] = (seed >> 128) % P   // draw_field
///   ch[0..7]  -> GKRExternalChallenges (6 perm-linearization + 1 additive)
///   ch[7..9]  -> [lookup_alpha, lookup_additive_part]
contract GkrStep1 {
    // Proth120: P = 7*2^120 + 1 (same modulus as whir.sol).
    uint256 constant P = 0x7000000000000000000000000000001;

    /// `preimage` is exactly the bytes the prover's `commit_initial_u32` hashed:
    /// `transcript_input` serialized as little-endian u32 words (top bits) followed
    /// by the raw 32-byte cap digests. Returns the post-commit seed and the 9 drawn
    /// field elements (already reduced mod P).
    function transcriptInit(bytes calldata preimage, uint64 nonce, uint32 powBits)
        external
        pure
        returns (bytes32 initialSeed, uint256[9] memory ch)
    {
        bytes32 seed = keccak256(preimage);
        initialSeed = seed;

        // PoW: new seed = keccak256(seed || be8(nonce)); its top `powBits` bits must be 0.
        seed = keccak256(abi.encodePacked(seed, nonce));
        if (powBits > 0) {
            require(uint256(seed) >> (256 - uint256(powBits)) == 0, "pow bits nonzero");
        }

        for (uint256 i = 0; i < 9; i++) {
            seed = keccak256(abi.encodePacked(seed));
            ch[i] = (uint256(seed) >> 128) % P;
        }
    }

    /// STEP 2a: the GKR dimension-reducing ENTRY. Continues the transcript past the
    /// 9 STEP-1 challenges, absorbs the circuit output evaluations, and draws the
    /// `numEvalPointCoords` eval-point coords + the batching challenge.
    /// `outputEvals` is the raw big-endian-16 packing of every output field element
    /// (exactly what `commit_field_els` absorbs). Returns the seed after those draws,
    /// the eval point, and the batching challenge.
    function gkrEntry(
        bytes calldata preimage,
        uint64 nonce,
        uint32 powBits,
        bytes calldata outputEvals,
        uint256 numEvalPointCoords
    )
        external
        pure
        returns (bytes32 seedOut, uint256[] memory evalPoint, uint256 batching)
    {
        bytes32 seed = keccak256(preimage);
        seed = keccak256(abi.encodePacked(seed, nonce));
        if (powBits > 0) {
            require(uint256(seed) >> (256 - uint256(powBits)) == 0, "pow bits nonzero");
        }
        // advance past the 9 STEP-1 challenges (values not needed here)
        for (uint256 i = 0; i < 9; i++) {
            seed = keccak256(abi.encodePacked(seed));
        }
        // absorb the output evaluations
        seed = keccak256(abi.encodePacked(seed, outputEvals));
        // draw eval-point coords, then the batching challenge
        evalPoint = new uint256[](numEvalPointCoords);
        for (uint256 i = 0; i < numEvalPointCoords; i++) {
            seed = keccak256(abi.encodePacked(seed));
            evalPoint[i] = (uint256(seed) >> 128) % P;
        }
        seed = keccak256(abi.encodePacked(seed));
        batching = (uint256(seed) >> 128) % P;
        seedOut = seed;
    }
}
