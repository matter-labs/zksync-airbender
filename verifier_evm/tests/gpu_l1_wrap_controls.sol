// SPDX-License-Identifier: MIT
pragma solidity =0.8.38;

import {TestRegistry} from "../src/TestRegistry.sol";
import {MergedBase} from "./MergedBase.sol";

contract GpuL1WrapControls is MergedBase {
    address verifier;

    function setUp() public {
        vm.etch(0x78D549f2A140923c517c23b008DFfE979B3c4E91, type(TestRegistry).runtimeCode);
        verifier = _deploy("out/GkrWhirVerifier.sol/GkrWhirVerifier.json");
    }

    function test_gpu_wrap_accepts() external {
        bytes memory proof = vm.readFileBinary(string.concat(DATA, "proof.bin"));
        bytes memory expected = _hex(string.concat(DATA, "verified_mark.hex"));
        require(keccak256(_accepts(verifier, proof)) == keccak256(expected), "verified mark");
    }

    function flip(string memory field, uint256 position) internal {
        bytes memory proof = vm.readFileBinary(string.concat(DATA, "proof.bin"));
        string memory map = vm.readFile(string.concat(DATA, "single_tx_calldata_fields.json"));
        string memory key = string.concat(".fields.", field);
        require(position < vm.parseJsonUint(map, string.concat(key, ".length")), "mutation field bounds");
        uint256 offset = vm.parseJsonUint(map, string.concat(key, ".offset"));
        proof[offset + position] ^= bytes1(uint8(1));
        require(_rejects(verifier, proof), field);
    }

    function test_gpu_wrap_rejects_changed_commitment() external { flip("whir_0_cap", 0); }
    function test_gpu_wrap_rejects_changed_ood() external { flip("whir_0_ood", 15); }
    function test_gpu_wrap_rejects_changed_nonce() external { flip("whir_0_pow_nonce", 7); }
    function test_gpu_wrap_rejects_changed_opening() external { flip("whir_0_query_0_memory_path", 0); }
}
