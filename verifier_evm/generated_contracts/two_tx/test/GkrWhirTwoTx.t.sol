// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// Two-transaction GKR/WHIR verification linked by a shared committed state, running the REAL
/// generated verifiers. GKR and WHIR live in sibling Foundry projects; this test reads their
/// compiled deployedBytecode and vm.etch's it, so the .sol source of truth is generated_contracts/.
///  - tx1: GKR verifier on gkr_full_calldata → committed state → mark_gkr_verified(commitment,..).
///  - tx2: WHIR verifier on its calldata → recomputes the same state → mark_whir_verified(commitment).
/// A consistent proof pair emits the SAME committed-state bytes32; the test asserts it.
///
/// Prereqs (a fresh `forge build` in each sibling): ../gkr and ../whir. See run_two_tx.sh.
///   forge test --match-contract GkrWhirTwoTxTest -vv

import {GkrWhirRegistry} from "../src/GkrWhirRegistry.sol";

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata s) external pure returns (bytes memory);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
    function etch(address who, bytes calldata code) external;
    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory);
}
struct Log { bytes32[] topics; bytes data; }

contract GkrWhirTwoTxTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    address constant REGISTRY = address(uint160(0xCAFE0001));
    address constant GKR = address(uint160(0x611b0001));
    address constant WHIR = address(uint160(0x11170001));

    event log_named_bytes32(string key, bytes32 val);

    function _calldata(string memory p) internal view returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", vm.readFile(p)));
    }

    // deployedBytecode.object from a sibling project's compiled artifact JSON.
    function _deployed(string memory artifactPath) internal view returns (bytes memory) {
        return vm.parseJsonBytes(vm.readFile(artifactPath), ".deployedBytecode.object");
    }

    function test_two_tx_linked_by_committed_state() external {
        // Registry at the fixed address both verifiers call; the two verifiers etched from the
        // sibling projects' compiled bytecode.
        GkrWhirRegistry impl = new GkrWhirRegistry();
        vm.etch(REGISTRY, address(impl).code);
        vm.etch(GKR, _deployed("../gkr/out/GkrVerifier.sol/GKRVerifier.json"));
        vm.etch(WHIR, _deployed("../whir/out/WhirVerifier.sol/WhirVerifier.json"));

        bytes memory gkrCd = _calldata("../../debug_data/gkr_full_calldata.hex");
        bytes memory whirCd = _calldata("../../debug_data/proth120_whir_calldata_from_proof.hex");

        // ---- tx1: GKR verifier ----
        vm.recordLogs();
        (bool ok1, ) = GKR.call(gkrCd);
        require(ok1, "GKR verifier reverted");
        Log[] memory l1 = vm.getRecordedLogs();
        require(l1.length == 1, "expected 1 GkrVerified event");
        bytes32 gkrCommit = l1[0].topics[1];

        // ---- tx2: WHIR verifier ----
        vm.recordLogs();
        (bool ok2, ) = WHIR.call(whirCd);
        require(ok2, "WHIR verifier reverted");
        Log[] memory l2 = vm.getRecordedLogs();
        require(l2.length == 1, "expected 1 WhirVerified event");
        bytes32 whirCommit = l2[0].topics[1];

        emit log_named_bytes32("gkr_committed_state", gkrCommit);
        emit log_named_bytes32("whir_committed_state", whirCommit);
        require(gkrCommit == whirCommit, "committed state mismatch between GKR and WHIR");
    }
}
