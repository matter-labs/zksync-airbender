// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// Two-transaction GKR/WHIR verification linked by a shared committed state, running the
/// REAL verifiers. gkr.sol (legacy) and whir.sol (via_ir) can't share a compile, so each is
/// precompiled to runtime bytecode (gkr_runtime.hex / whir_runtime.hex) and vm.etch'd here.
///  - tx1: GKR verifier on gkr_full_calldata → computes committed state → mark_gkr_verified.
///  - tx2: WHIR verifier on its calldata → recomputes the same state → mark_whir_verified.
/// A consistent proof pair emits the SAME bytes32; the test asserts it and prints real gas.
///   forge test -C circuit_e2e --match-contract GkrWhirTwoTxTest -vv

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata s) external pure returns (bytes memory);
    function etch(address who, bytes calldata code) external;
    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory);
}
struct Log { bytes32[] topics; bytes data; }

contract GkrWhirRegistry {
    event GkrVerified(bytes32 indexed commitment);
    event WhirVerified(bytes32 indexed commitment);
    function mark_gkr_verified(bytes32 c) external { emit GkrVerified(c); }
    function mark_whir_verified(bytes32 c) external { emit WhirVerified(c); }
}

contract GkrWhirTwoTxTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    address constant REGISTRY = address(uint160(0xCAFE0001));
    address constant GKR = address(uint160(0x611b0001));
    address constant WHIR = address(uint160(0x11170001));

    event log_named_uint(string key, uint256 val);
    event log_named_bytes32(string key, bytes32 val);

    function _rd(string memory p) internal view returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", vm.readFile(p)));
    }

    function test_two_tx_linked_by_committed_state() external {
        // deploy the registry at the fixed address both verifiers call, etch the two verifiers
        GkrWhirRegistry impl = new GkrWhirRegistry();
        vm.etch(REGISTRY, address(impl).code);
        vm.etch(GKR, _rd("gkr_runtime.hex"));
        vm.etch(WHIR, _rd("whir_runtime.hex"));

        bytes memory gkrCd = _rd("../whir/testdata/gkr_full_calldata.hex");
        bytes memory whirCd = _rd("../whir/testdata/proth120_whir_calldata_from_proof.hex");

        // ---- tx1: GKR verifier ----
        vm.recordLogs();
        uint256 g1 = gasleft();
        (bool ok1, ) = GKR.call(gkrCd);
        uint256 gkrGas = g1 - gasleft();
        require(ok1, "GKR verifier reverted");
        Log[] memory l1 = vm.getRecordedLogs();
        require(l1.length == 1, "expected 1 GkrVerified event");
        bytes32 gkrCommit = l1[0].topics[1];

        // ---- tx2: WHIR verifier ----
        vm.recordLogs();
        uint256 g2 = gasleft();
        (bool ok2, ) = WHIR.call(whirCd);
        uint256 whirGas = g2 - gasleft();
        require(ok2, "WHIR verifier reverted");
        Log[] memory l2 = vm.getRecordedLogs();
        require(l2.length == 1, "expected 1 WhirVerified event");
        bytes32 whirCommit = l2[0].topics[1];

        emit log_named_bytes32("gkr_committed_state", gkrCommit);
        emit log_named_bytes32("whir_committed_state", whirCommit);
        require(gkrCommit == whirCommit, "committed state mismatch between GKR and WHIR");
        emit log_named_uint("COMMITTED STATES MATCH", 1);

        // NOTE: gkrGas/whirGas here are the gasleft() delta around an in-harness external
        // CALL passing `bytes memory` as args — this over-counts vs a real transaction (which
        // reads the proof from tx calldata via CALLDATALOAD, never memory). For accurate
        // per-tx gas run circuit_e2e/raw_tx_gas.sh (raw anvil transactions):
        //   GKR  execution 1,232,458  -> tx 1,743,650 (execution-bound)
        //   WHIR execution 1,828,992  -> tx 3,069,320 (EIP-7623 calldata-floor-bound)
        gkrGas; whirGas;
    }
}
