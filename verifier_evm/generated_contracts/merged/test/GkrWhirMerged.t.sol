// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// Single-transaction GKR+WHIR verification with the merged `GkrWhirVerifier`: one call on
/// `merged_calldata.hex` (= GKR stream ‖ WHIR proof stream). The contract hands the WHIR start
/// state over in memory, so there is no committed state and no registry; success is the
/// `Verified(public_input, setup_commitment)` event. The test checks the event payload against
/// the final registers in the calldata preimage (x10..x17 / x18..x25, LE u32 at byte reg*12) —
/// the same extraction the two-tx registry marks use — so it is proof-agnostic.
///
/// Prereq: `forge build` here (the verifier is compiled in this project).
///   forge test -vv                 (pure execution gas: --no-isolate)
///   forge test -vv --isolate       (tx-level gas incl. intrinsic + EIP-7623 floor)

import {GkrWhirVerifier} from "../src/GkrWhirVerifier.sol";

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata s) external pure returns (bytes memory);
    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory);
}
struct Log { bytes32[] topics; bytes data; }

contract GkrWhirMergedTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    bytes32 constant VERIFIED_TOPIC = keccak256("Verified(bytes32,bytes32)");

    event log_named_uint(string key, uint256 val);
    event log_named_bytes32(string key, bytes32 val);

    function _calldata(string memory p) internal view returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", vm.readFile(p)));
    }

    // 8 registers' u32 values, each stored LE at calldata byte `reg*12`, concatenated.
    function _registers(bytes memory cd, uint256 firstReg) internal pure returns (bytes32 out) {
        for (uint256 i = 0; i < 8; ++i) {
            uint256 off = (firstReg + i) * 12;
            for (uint256 b = 0; b < 4; ++b) {
                out |= bytes32(uint256(uint8(cd[off + b])) << (8 * (31 - (i * 4 + b))));
            }
        }
    }

    function test_merged_single_tx() external {
        GkrWhirVerifier v = new GkrWhirVerifier();
        bytes memory cd = _calldata("../../debug_data/merged_calldata.hex");
        emit log_named_uint("calldata_bytes", cd.length);

        vm.recordLogs();
        uint256 g = gasleft();
        (bool ok, bytes memory ret) = address(v).call(cd);
        g -= gasleft();
        require(ok, "merged verifier reverted");

        // collect the verifier's logs BEFORE emitting any of our own (they would be recorded too)
        Log[] memory l = vm.getRecordedLogs();
        emit log_named_uint("verifier_call_gas", g);
        require(l.length == 1, "expected exactly 1 Verified event");
        require(l[0].topics.length == 1 && l[0].topics[0] == VERIFIED_TOPIC, "wrong event");
        (bytes32 public_input, bytes32 setup_commitment) = abi.decode(l[0].data, (bytes32, bytes32));
        emit log_named_bytes32("public_input", public_input);
        emit log_named_bytes32("setup_commitment", setup_commitment);
        require(public_input == _registers(cd, 10), "public_input != registers x10..x17");
        require(setup_commitment == _registers(cd, 18), "setup_commitment != registers x18..x25");
        require(ret.length == 64, "unexpected return size");
    }
}
