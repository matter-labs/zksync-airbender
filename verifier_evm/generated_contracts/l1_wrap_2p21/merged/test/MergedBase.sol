// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

import {IVerificationRegistry} from "../src/GkrWhirVerifier.sol";

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata value) external pure returns (bytes memory);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
    function parseJsonUint(string calldata json, string calldata key) external pure returns (uint256);
    function parseJsonString(string calldata json, string calldata key) external pure returns (string memory);
    function toString(uint256 value) external pure returns (string memory);
    function etch(address target, bytes calldata code) external;
}

/// A registry that refuses every mark.
contract RevertingRegistry is IVerificationRegistry {
    function markVerified(bytes32, bytes32, bytes32) external pure override {
        revert("refused");
    }
}

/// Shared helpers: versioned data, and deployment of the renders built in sibling projects
/// (`../merged_f1`, `../negative/*`, `../controls/*`, `../instrumented/*`) from their creation
/// code, with the registry as the constructor argument.
abstract contract MergedBase {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    string constant DATA = "../../../debug_data/l1_wrap_2p21/";
    uint256 constant EIP170 = 24_576;
    /// The F1 verifier's pinned `SetupFrontier` address (generate_contracts' DEFAULT_FRONTIER_ADDRESS).
    address constant FRONTIER = 0x5FbDB2315678afecb367f032d93F642f64180aa3;

    function _hex(string memory path) internal view returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", vm.readFile(path)));
    }

    function _creation(string memory artifact) internal view returns (bytes memory code) {
        code = vm.parseJsonBytes(vm.readFile(artifact), ".bytecode.object");
        require(code.length != 0, "missing generated verifier bytecode (forge build its project)");
    }

    function _deploy(string memory artifact, address registry) internal returns (address v) {
        bytes memory init = bytes.concat(_creation(artifact), abi.encode(registry));
        assembly ("memory-safe") {
            v := create(0, add(init, 32), mload(init))
        }
        require(v != address(0), "verifier deployment failed");
    }

    /// Deploys the F1 verifier's `SetupFrontier` and places its code at the pinned address.
    function _placeFrontier() internal {
        _placeFrontier("../merged_f1");
    }

    /// Deploys the `SetupFrontier` of the render project `project` at the pinned address.
    function _placeFrontier(string memory project) internal {
        bytes memory init = _creation(string.concat(project, "/out/SetupFrontier.sol/SetupFrontier.json"));
        address f;
        assembly ("memory-safe") {
            f := create(0, add(init, 32), mload(init))
        }
        require(f != address(0), "frontier deployment failed");
        vm.etch(FRONTIER, f.code);
    }

    function _slice(bytes memory b, uint256 from, uint256 to) internal pure returns (bytes memory out) {
        out = new bytes(to - from);
        for (uint256 i; i < out.length; ++i) {
            out[i] = b[from + i];
        }
    }

    function _copy(bytes memory b) internal pure returns (bytes memory) {
        return _slice(b, 0, b.length);
    }

    function _slice32(bytes memory b, uint256 off) internal pure returns (bytes32 out) {
        assembly ("memory-safe") {
            out := mload(add(add(b, 32), off))
        }
    }

    function _accepts(address v, bytes memory data) internal returns (bytes memory ret) {
        bool ok;
        (ok, ret) = v.call(data);
        require(ok, "unmodified proof must verify");
    }

    function _rejects(address v, bytes memory data) internal returns (bool) {
        (bool ok,) = v.call(data);
        return !ok;
    }
}
