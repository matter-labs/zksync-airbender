// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata s) external pure returns (bytes memory);
}

/// Validates the gkr.sol `gkr_init` Yul (GKR entry, STEP 2a) against the reference values
/// pinned by the on-chain-validated GkrStep1.gkrEntry. Runs transcript_init (9 STEP-1 draws)
/// then gkr_init (absorb 2560 B of output evals, draw eval_point[4] + batching) on the REAL
/// preimage + output-eval fixtures, and asserts seed / eval_point / batching match.
///   forge test --match-contract GkrInitYulTest -vv
contract GkrInitYulTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    uint256 constant P = 0x7000000000000000000000000000001;
    uint256 constant PLEN = 520;   // preimage bytes
    uint256 constant OUTS = 2560;  // output-eval bytes

    function _rd(string memory p) internal view returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", vm.readFile(p)));
    }

    function test_gkr_init_matches_reference() external {
        bytes memory preimage = _rd("../whir/testdata/gkr_step1_preimage.hex");
        bytes memory outs = _rd("../whir/testdata/gkr_step2_output_evals.hex");
        require(preimage.length == PLEN && outs.length == OUTS, "fixture sizes");
        // cd = preimage || outputEvals (contiguous, exactly the gkr.sol stream order)
        bytes memory cd = bytes.concat(preimage, outs);

        bytes32 seedOut;
        bytes32 commitSeed;
        uint256[4] memory z;
        uint256 batching;
        assembly {
            let cdp := add(cd, 32) // data pointer of `cd`

            // ---- transcript_init: keccak(preimage) -> PoW fold -> 9 STEP-1 draws ----
            let seed := keccak256(cdp, PLEN)
            commitSeed := seed
            // scratch for the PoW fold + draws: the Solidity free-memory pointer (guaranteed free)
            let S := mload(0x40)
            mstore(S, seed)
            mstore(add(S, 32), 0) // 8-byte nonce = 0 (pow_bits = 0, no check)
            seed := keccak256(S, 40)
            mstore(S, seed)
            for { let i := 0 } lt(i, 9) { i := add(i, 1) } {
                seed := keccak256(S, 32)
                mstore(S, seed)
            }

            // ---- gkr_init: absorb output evals, draw eval_point[4] + batching ----
            // keccak(seed || outputEvals): place seed just before the outputs in cd
            // (overwriting the already-consumed tail of the preimage), then hash 32+2560.
            mstore(add(cdp, sub(PLEN, 32)), seed)
            seed := keccak256(add(cdp, sub(PLEN, 32)), add(32, OUTS))
            mstore(S, seed)
            // 4 eval-point coords, then batching (each: keccak(seed); top-128 mod P)
            seed := keccak256(S, 32) mstore(S, seed) mstore(z,             mod(shr(128, seed), P))
            seed := keccak256(S, 32) mstore(S, seed) mstore(add(z, 32),    mod(shr(128, seed), P))
            seed := keccak256(S, 32) mstore(S, seed) mstore(add(z, 64),    mod(shr(128, seed), P))
            seed := keccak256(S, 32) mstore(S, seed) mstore(add(z, 96),    mod(shr(128, seed), P))
            seed := keccak256(S, 32) mstore(S, seed) batching := mod(shr(128, seed), P)
            seedOut := seed
        }

        require(
            commitSeed == 0x26509dbe5c7a38348f24997eca31f7c9fbec8d61f4d8a0038292836975f1d62a,
            "commit seed (keccak preimage) mismatch"
        );
        require(z[0] == 0x0515af1d43ebb20064c5512658017079, "z0");
        require(z[1] == 0x01383e3972ccf84ac8d79d0e5b53a05b, "z1");
        require(z[2] == 0x01852fd86551ceb9c7ead07de80d0819, "z2");
        require(z[3] == 0x002901dac4244987983f17e14a18ca7b, "z3");
        require(batching == 0x06fe013de0865662236dfa43310540af, "batching");
        require(
            seedOut == 0x37fe013de0865662236dfa43310540b6e628ae629be4da583fabaf681c9da480,
            "seed mismatch"
        );
    }
}
