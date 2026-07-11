// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "./GkrStep1.sol";

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata s) external pure returns (bytes memory);
}

/// Executes the STEP-1 transcript against the prover-generated fixture and checks
/// the derived seed + 9 challenges against the reference captured by the Rust test
/// `validate_packed_transcript_recipe` (see gkr_transcript_reference.md).
/// Run: `forge test --match-contract GkrStep1Test`
contract GkrStep1Test {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function test_transcript_matches_prover() external {
        GkrStep1 c = new GkrStep1();

        string memory h = vm.readFile("../whir/testdata/gkr_step1_preimage.hex");
        bytes memory preimage = vm.parseBytes(string.concat("0x", h));

        (bytes32 seed, uint256[9] memory ch) = c.transcriptInit(preimage, 0, 0);

        require(
            seed == 0x26509dbe5c7a38348f24997eca31f7c9fbec8d61f4d8a0038292836975f1d62a,
            "initial seed mismatch"
        );

        uint256[9] memory expected = [
            uint256(0x069daed5dbcc43f1a7b83e738e6000a0),
            0x032dad98f0c5fae7307259608a67ac6e,
            0x053efcfc827ed9003e569e68329cb736,
            0x06dadad22ecbaed9e13f9141f6a7b981,
            0x0110efef202b58876924c46309615d05,
            0x05cf1667ee0389f548469e0ccb27f685,
            0x06a76fd69d68798f727ab895b707ac52,
            0x02a48105e1ef1781ab2fc61d5e007ebf,
            0x02d32afd101f3211f4f2f705bf194b54
        ];
        for (uint256 i = 0; i < 9; i++) {
            require(ch[i] == expected[i], "challenge mismatch");
        }
    }

    function test_gkr_entry_matches_prover() external {
        GkrStep1 c = new GkrStep1();

        bytes memory preimage =
            vm.parseBytes(string.concat("0x", vm.readFile("../whir/testdata/gkr_step1_preimage.hex")));
        bytes memory outputEvals =
            vm.parseBytes(string.concat("0x", vm.readFile("../whir/testdata/gkr_step2_output_evals.hex")));

        (bytes32 seedOut, uint256[] memory evalPoint, uint256 batching) =
            c.gkrEntry(preimage, 0, 0, outputEvals, 4);

        require(
            seedOut == 0x37fe013de0865662236dfa43310540b6e628ae629be4da583fabaf681c9da480,
            "entry seed mismatch"
        );
        require(evalPoint.length == 4, "eval point len");
        require(evalPoint[0] == 0x0515af1d43ebb20064c5512658017079, "ep0");
        require(evalPoint[1] == 0x01383e3972ccf84ac8d79d0e5b53a05b, "ep1");
        require(evalPoint[2] == 0x01852fd86551ceb9c7ead07de80d0819, "ep2");
        require(evalPoint[3] == 0x002901dac4244987983f17e14a18ca7b, "ep3");
        require(batching == 0x06fe013de0865662236dfa43310540af, "batching");
    }
}
