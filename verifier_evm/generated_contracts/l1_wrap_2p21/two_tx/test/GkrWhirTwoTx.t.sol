// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

import {GkrWhirRegistry} from "../src/GkrWhirRegistry.sol";

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata value) external pure returns (bytes memory);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
    function parseJsonUint(string calldata json, string calldata key) external pure returns (uint256);
    function parseJsonString(string calldata json, string calldata key) external pure returns (string memory);
    function etch(address target, bytes calldata code) external;
    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory);
}

struct Log {
    bytes32[] topics;
    bytes data;
}

/// Requires the real generated 2p21 contracts, proof calldata and field metadata.
/// setUp fails if any artifact is missing; the independent registry suite can run earlier.
contract GkrWhirTwoTxTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    address constant REGISTRY = address(uint160(0xCAFE0001));
    address constant GKR = address(uint160(0x611b0001));
    address constant WHIR = address(uint160(0x11170001));
    string constant DATA = "../../../debug_data/l1_wrap_2p21/";
    bytes gkrCalldata;
    bytes whirCalldata;
    string fields;

    function _calldata(string memory path) internal view returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", vm.readFile(path)));
    }

    function _deployed(string memory path) internal view returns (bytes memory code) {
        code = vm.parseJsonBytes(vm.readFile(path), ".deployedBytecode.object");
        require(code.length != 0, "missing generated verifier bytecode");
    }

    function setUp() public {
        GkrWhirRegistry impl = new GkrWhirRegistry(address(this));
        vm.etch(REGISTRY, address(impl).code);
        vm.etch(GKR, _deployed("../gkr/out/GkrVerifier.sol/GKRVerifier.json"));
        vm.etch(WHIR, _deployed("../whir/out/WhirVerifier.sol/WhirVerifier.json"));
        GkrWhirRegistry(REGISTRY).initialize_verifiers(GKR, WHIR);
        gkrCalldata = _calldata(string.concat(DATA, "gkr_full_calldata.hex"));
        whirCalldata = _calldata(string.concat(DATA, "proth120_whir_calldata_from_proof.hex"));
        fields = vm.readFile(string.concat(DATA, "calldata_fields.json"));
    }

    function _verifyPair() internal {
        vm.recordLogs();
        (bool gkrOk,) = GKR.call(gkrCalldata);
        require(gkrOk, "unmodified GKR proof must verify");
        Log[] memory gkrLogs = vm.getRecordedLogs();
        require(gkrLogs.length == 1, "expected one GKR mark");
        bytes32 commitment = gkrLogs[0].topics[1];
        vm.recordLogs();
        (bool whirOk,) = WHIR.call(whirCalldata);
        require(whirOk, "unmodified WHIR proof must verify");
        Log[] memory whirLogs = vm.getRecordedLogs();
        require(whirLogs.length == 1, "expected one WHIR mark");
        require(whirLogs[0].topics[1] == commitment, "committed states differ");
        require(
            GkrWhirRegistry(REGISTRY).verificationMask(commitment) == GkrWhirRegistry.VerificationMask.Both,
            "pair was not accepted"
        );
    }

    /// The serializer records each field's offset, encoding and expected bytes.
    /// Validate that semantic field before changing its last byte; no fixture offsets live here.
    function _flipField(bytes memory payload, string memory key, uint256 width, string memory encoding) internal view {
        uint256 offset = vm.parseJsonUint(fields, string.concat(key, ".offset"));
        bytes memory expected = vm.parseJsonBytes(fields, string.concat(key, ".bytes"));
        require(
            keccak256(bytes(vm.parseJsonString(fields, string.concat(key, ".encoding")))) == keccak256(bytes(encoding)),
            "wrong field encoding"
        );
        require(expected.length == width && offset + width <= payload.length, "wrong field bounds");
        for (uint256 i; i < width; ++i) {
            require(payload[offset + i] == expected[i], "field differs from proof metadata");
        }
        payload[offset + width - 1] ^= bytes1(uint8(1));
        require(payload[offset + width - 1] != expected[width - 1], "field was not mutated");
    }

    function test_two_tx_linked_by_committed_state() public {
        _verifyPair();
    }

    function test_rejects_flipped_opening_byte() public {
        _verifyPair();
        bytes memory bad = whirCalldata;
        _flipField(bad, ".whir.batched_opening", 16, "proth120_be");
        (bool ok,) = WHIR.call(bad);
        require(!ok, "changed WHIR opening accepted");
    }

    function test_rejects_wrong_pow_nonce() public {
        _verifyPair();
        bytes memory bad = gkrCalldata;
        _flipField(bad, ".gkr.external_pow_nonce", 8, "u64_be");
        (bool ok,) = GKR.call(bad);
        require(!ok, "changed external PoW nonce accepted");
    }

    function test_rejects_wrong_final_pc() public {
        _verifyPair();
        bytes memory bad = gkrCalldata;
        _flipField(bad, ".gkr.final_pc", 4, "u32_le");
        // This also changes the transcript seed; rejection may precede the explicit PC check.
        (bool ok,) = GKR.call(bad);
        require(!ok, "changed final PC accepted");
    }

    function test_rejects_2p22_proof() public {
        _verifyPair();
        (bool gkrOk,) = GKR.call(_calldata("../../../debug_data/gkr_full_calldata.hex"));
        require(!gkrOk, "2p22 GKR proof accepted by 2p21 verifier");
        (bool whirOk,) = WHIR.call(_calldata("../../../debug_data/proth120_whir_calldata_from_proof.hex"));
        require(!whirOk, "2p22 WHIR proof accepted by 2p21 verifier");
    }
}
