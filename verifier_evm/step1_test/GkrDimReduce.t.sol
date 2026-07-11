// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "./GkrDimReduce.sol";

interface Vm2 {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata s) external pure returns (bytes memory);
}

/// Runs the full dimension-reducing verification (18 layers) against the prover
/// fixtures and checks the post-dim-reduce seed + batching + point length against the
/// reference captured by the Rust test `verify_dim_reduce_layers`.
/// Run: `forge test --match-contract GkrDimReduceTest`
contract GkrDimReduceTest {
    Vm2 constant vm = Vm2(address(uint160(uint256(keccak256("hevm cheat code")))));

    function _rd(string memory p) internal view returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", vm.readFile(p)));
    }

    function test_dim_reduce_matches_prover() external {
        GkrDimReduce c = new GkrDimReduce();

        bytes memory preimage = _rd("../whir/testdata/gkr_step1_preimage.hex");
        bytes memory outputEvals = _rd("../whir/testdata/gkr_step2_output_evals.hex");
        bytes memory blob = _rd("../whir/testdata/gkr_dimreduce_data.hex");

        (bytes32 seedOut, uint256 batchingOut, uint256 pointLen) =
            c.verifyDimReduce(preimage, 0, 0, outputEvals, 4, blob);

        require(pointLen == 22, "point length");
        require(
            batchingOut == 0x06616d7d0fe9664e9ad006cc97f250ae,
            "batching mismatch"
        );
        require(
            seedOut == 0xc3616d7d0fe9664e9ad006cc97f250c978fde8d241a2d9d467b73925d8c28fe0,
            "seed mismatch"
        );
    }
}
