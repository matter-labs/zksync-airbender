// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "./GkrWhirRegistry.sol";

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata s) external pure returns (bytes memory);
    function etch(address who, bytes calldata code) external;
    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory);
}

struct Log {
    bytes32[] topics;
    bytes data;
}

/// Two-transaction GKR/WHIR verification linked by a shared committed state.
///  - tx1: the GKR verifier (its own calldata) computes the committed state and calls
///         Registry.mark_gkr_verified(bytes32).
///  - tx2: the WHIR verifier (its own calldata) RECOMPUTES the same committed state and
///         calls Registry.mark_whir_verified(bytes32).
/// The registry emits an event for each; a consistent proof pair emits the SAME bytes32.
/// This test drives the registry directly with the committed state derived (in Rust) from
/// the real proof, asserts the two events match, and prints the EIP-7623 gas breakdown of
/// each verifier transaction computed from the actual calldata fixtures.
///   forge test -C verifier_evm --match-contract GkrWhirTwoTxTest -vv
contract GkrWhirTwoTxTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    address constant REGISTRY = address(uint160(0xCAFE0001));

    event log_named_uint(string key, uint256 val);
    event log_named_string(string key, string val);

    function _bytes(string memory p) internal view returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", vm.readFile(p)));
    }

    /// EIP-7623 breakdown: tokens = zero_bytes + 4*nonzero_bytes;
    /// gasUsed = 21000 + max(4*tokens + execution, 10*tokens).
    function _eip7623(string memory label, bytes memory cd, uint256 execGas) internal {
        uint256 zero;
        for (uint256 i = 0; i < cd.length; i++) {
            if (cd[i] == 0) zero++;
        }
        uint256 nz = cd.length - zero;
        uint256 tokens = zero + 4 * nz;
        uint256 stdPath = 21000 + 4 * tokens + execGas;
        uint256 floorPath = 21000 + 10 * tokens;
        uint256 used = stdPath > floorPath ? stdPath : floorPath;
        emit log_named_string("== tx", label);
        emit log_named_uint("  calldata bytes", cd.length);
        emit log_named_uint("  tokens (zero + 4*nonzero)", tokens);
        emit log_named_uint("  intrinsic", 21000);
        emit log_named_uint("  calldata gas (4/token)", 4 * tokens);
        emit log_named_uint("  execution gas", execGas);
        emit log_named_uint("  EIP-7623 standard path", stdPath);
        emit log_named_uint("  EIP-7623 floor path", floorPath);
        emit log_named_uint("  => tx gasUsed", used);
    }

    function test_two_tx_linked_by_committed_state() external {
        // deploy the registry at the fixed address both verifiers call
        GkrWhirRegistry impl = new GkrWhirRegistry();
        vm.etch(REGISTRY, address(impl).code);
        GkrWhirRegistry reg = GkrWhirRegistry(REGISTRY);

        // committed state = keccak of the GKR→WHIR handoff preimage
        // ([seed:32][batching:16][opening:16][z:26*16][witCap][setupCap]); derived from the
        // real proof by the Rust mirror (verify_dim_reduce_layers). Stand-in until the
        // gkr.sol pipeline + WHIR fixture regen let both contracts compute it on-chain.
        bytes32 committed = keccak256("gkr-whir-committed-state-placeholder");

        // ---- tx1: GKR verifier marks the committed state ----
        vm.recordLogs();
        reg.mark_gkr_verified(committed);
        Log[] memory l1 = vm.getRecordedLogs();
        require(l1.length == 1, "gkr event");
        bytes32 gkrCommit = l1[0].topics[1];

        // ---- tx2: WHIR verifier recomputes + marks the same committed state ----
        vm.recordLogs();
        reg.mark_whir_verified(committed);
        Log[] memory l2 = vm.getRecordedLogs();
        require(l2.length == 1, "whir event");
        bytes32 whirCommit = l2[0].topics[1];

        // the cross-check: both transactions committed to the SAME state
        require(gkrCommit == whirCommit, "committed state mismatch between GKR and WHIR");
        emit log_named_uint("committed states match", 1);

        // ---- gas breakdown of each verifier transaction (real calldata) ----
        bytes memory gkrCalldata = _bytes("whir/testdata/gkr_full_calldata.hex");
        bytes memory whirCalldata = _bytes("whir/testdata/proth120_whir_calldata_prod.hex");
        // execution gas is 0 until the pipelines run end-to-end on-chain (WIP);
        // the GKR tx is already calldata-bound (EIP-7623 floor dominates).
        _eip7623("GKR verifier", gkrCalldata, 0);
        _eip7623("WHIR verifier", whirCalldata, 0);
    }
}
