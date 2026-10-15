// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata value) external pure returns (bytes memory);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
    function parseJsonUint(string calldata json, string calldata key) external pure returns (uint256);
    function etch(address target, bytes calldata code) external;
}

/// F1 ↔ v0 oracle: the instrumented renders log every keccak256 result (transcript absorbs and
/// draws, PoW digests, query draws, leaf and Merkle hashes, the committed state) and return
/// [count][hashes][own return data]. On the same proof, the F1 verifiers must produce the v0
/// verifiers' log and results.
contract F1OracleTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    address constant GKR_V0 = address(uint160(0x611b0102));
    address constant GKR_F1 = address(uint160(0x611b0112));
    address constant WHIR_V0 = address(uint160(0x11170102));
    address constant WHIR_F1 = address(uint160(0x11170112));
    string constant DATA = "../../../../debug_data/l1_wrap_2p21/";
    bytes v0Gkr;
    bytes v0Whir;
    bytes f1;
    uint256 gkrBytes;

    function _calldata(string memory path) internal view returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", vm.readFile(path)));
    }

    function _deployed(string memory path) internal view returns (bytes memory code) {
        code = vm.parseJsonBytes(vm.readFile(path), ".deployedBytecode.object");
        require(code.length != 0, "missing generated verifier bytecode");
    }

    function _slice(bytes memory b, uint256 from, uint256 to) internal pure returns (bytes memory out) {
        out = new bytes(to - from);
        for (uint256 i; i < out.length; ++i) {
            out[i] = b[from + i];
        }
    }

    function setUp() public {
        vm.etch(GKR_V0, _deployed("../instrumented/gkr_v0/out/GkrVerifier.sol/GKRVerifier.json"));
        vm.etch(GKR_F1, _deployed("../instrumented/gkr_f1/out/GkrVerifier.sol/GKRVerifier.json"));
        vm.etch(WHIR_V0, _deployed("../instrumented/whir_v0/out/WhirVerifier.sol/WhirVerifier.json"));
        vm.etch(WHIR_F1, _deployed("../instrumented/whir_f1/out/WhirVerifier.sol/WhirVerifier.json"));
        v0Gkr = _calldata(string.concat(DATA, "gkr_full_calldata.hex"));
        v0Whir = _calldata(string.concat(DATA, "proth120_whir_calldata_from_proof.hex"));
        f1 = _calldata(string.concat(DATA, "single_tx_f1.hex"));
        gkrBytes = vm.parseJsonUint(vm.readFile(string.concat(DATA, "single_tx_f1_fields.json")), ".gkr_bytes");
    }

    function _run(address verifier, bytes memory data) internal returns (bytes memory log, bytes memory result) {
        (bool ok, bytes memory ret) = verifier.call(data);
        require(ok, "instrumented verifier must accept the unmodified proof");
        uint256 count;
        assembly {
            count := mload(add(ret, 32))
        }
        uint256 head = 32 * (count + 1);
        require(count > 0 && ret.length >= head, "malformed instrumented return");
        log = _slice(ret, 0, head);
        result = _slice(ret, head, ret.length);
    }

    function test_gkr_log_and_result_equal_v0() public {
        (bytes memory log0, bytes memory res0) = _run(GKR_V0, v0Gkr);
        (bytes memory log1, bytes memory res1) = _run(GKR_F1, _slice(f1, 0, gkrBytes));
        require(keccak256(log0) == keccak256(log1), "GKR keccak log differs");
        require(keccak256(res0) == keccak256(res1), "GKR result differs");
    }

    /// WHIR input = the committed-state header the GKR verifier returns ‖ the WHIR proof stream.
    /// Results are [claim][verify_gas][cd][commitment]; verify_gas and cd differ by construction.
    function test_whir_log_and_claim_equal_v0() public {
        uint256 header = 976; // == the preimage the GKR verifier returns (SingleTxTest.setUp)
        (bytes memory log0, bytes memory res0) = _run(WHIR_V0, v0Whir);
        bytes memory f1Whir = bytes.concat(_slice(v0Whir, 0, header), _slice(f1, gkrBytes, f1.length));
        (bytes memory log1, bytes memory res1) = _run(WHIR_F1, f1Whir);
        require(keccak256(log0) == keccak256(log1), "WHIR keccak log differs");
        require(res0.length == 128 && res1.length == 128, "WHIR result size");
        require(keccak256(_slice(res0, 0, 32)) == keccak256(_slice(res1, 0, 32)), "WHIR claim differs");
        require(keccak256(_slice(res0, 96, 128)) == keccak256(_slice(res1, 96, 128)), "WHIR commitment differs");
    }
}
