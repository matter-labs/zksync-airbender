// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

import {L1VerifierSingleTx} from "../src/L1VerifierSingleTx.sol";
import {SetupFrontier} from "f1_frontier/SetupFrontier.sol";

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata value) external pure returns (bytes memory);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
    function parseJsonUint(string calldata json, string calldata key) external pure returns (uint256);
    function toString(uint256 value) external pure returns (string memory);
    function etch(address target, bytes calldata code) external;
}

/// Format F1 (verifier_evm::encoding) on the generated F1 verifiers, against the v0 single-tx
/// verifiers on the same proof.
contract F1SingleTxTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    address constant GKR_V0 = address(uint160(0x611b0002));
    address constant WHIR_V0 = address(uint160(0x11170002));
    address constant GKR_F1 = address(uint160(0x611b0012));
    address constant GKR_F1_WRONG_PC = address(uint160(0x611b0013));
    address constant WHIR_F1 = address(uint160(0x11170012));
    address constant GKR_F1_WRONG_SETUP_CAP = address(uint160(0x611b0014));
    address constant FRONTIER = address(uint160(0x5e7f0001)); // the F1 WHIR verifier's frontier constant
    string constant DATA = "../../../../debug_data/l1_wrap_2p21/";
    bytes v0Gkr;
    bytes v0Whir;
    bytes f1;
    uint256 gkrBytes;
    string fields;
    L1VerifierSingleTx proxyV0;
    L1VerifierSingleTx proxyF1;

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
        vm.etch(GKR_V0, _deployed("../gkr/out/GkrVerifier.sol/GKRVerifier.json"));
        vm.etch(WHIR_V0, _deployed("../whir/out/WhirVerifier.sol/WhirVerifier.json"));
        vm.etch(GKR_F1, _deployed("../f1/gkr/out/GkrVerifier.sol/GKRVerifier.json"));
        vm.etch(GKR_F1_WRONG_PC, _deployed("../f1/gkr_negative/out/GkrVerifierWrongFinalPc.sol/GKRVerifier.json"));
        vm.etch(WHIR_F1, _deployed("../f1/whir/out/WhirVerifier.sol/WhirVerifier.json"));
        vm.etch(FRONTIER, address(new SetupFrontier()).code);
        vm.etch(
            GKR_F1_WRONG_SETUP_CAP,
            _deployed("../f1/gkr_wrong_setup_cap/out/GkrVerifierWrongSetupCap.sol/GKRVerifier.json")
        );
        v0Gkr = _calldata(string.concat(DATA, "gkr_full_calldata.hex"));
        v0Whir = _calldata(string.concat(DATA, "proth120_whir_calldata_from_proof.hex"));
        f1 = _calldata(string.concat(DATA, "single_tx_f1.hex"));
        fields = vm.readFile(string.concat(DATA, "single_tx_f1_fields.json"));
        gkrBytes = vm.parseJsonUint(fields, ".gkr_bytes");
        require(vm.parseJsonUint(fields, ".bytes") == f1.length, "F1 calldata and field map disagree");
        proxyV0 = new L1VerifierSingleTx(GKR_V0, WHIR_V0, v0Gkr.length);
        proxyF1 = new L1VerifierSingleTx(GKR_F1, WHIR_F1, gkrBytes);
    }

    function _field(string memory name) internal view returns (uint256 offset, uint256 length) {
        offset = vm.parseJsonUint(fields, string.concat(".fields.", name, ".offset"));
        length = vm.parseJsonUint(fields, string.concat(".fields.", name, ".length"));
    }

    function _accepts(L1VerifierSingleTx v, bytes memory data) internal returns (bytes memory ret) {
        bool ok;
        (ok, ret) = address(v).call(data);
        require(ok, "unmodified single-tx proof must verify");
    }

    function _rejects(L1VerifierSingleTx v, bytes memory data) internal returns (bool) {
        (bool ok,) = address(v).call(data);
        return !ok;
    }

    function _copy(bytes memory b) internal pure returns (bytes memory) {
        return _slice(b, 0, b.length);
    }

    /// Flip the least significant bit of element `j` of the FE-run `name` (stays canonical
    /// unless the element is p − 1).
    function _flipElement(string memory name, uint256 j) internal view returns (bytes memory m) {
        (uint256 offset, uint256 length) = _field(name);
        uint256 bit = 123 * j + 122;
        require(bit < 8 * length, "element out of run");
        m = _copy(f1);
        m[offset + bit / 8] ^= bytes1(uint8(0x80 >> (bit % 8)));
    }

    /// Flip the least significant bit of the last element of the FE-run `name`.
    function _flipLastElement(string memory name) internal view returns (bytes memory m) {
        (, uint256 length) = _field(name);
        return _flipElement(name, 8 * length / 123 - 1);
    }

    function _finalRound(string memory suffix) internal view returns (string memory) {
        return string.concat("whir_", vm.toString(vm.parseJsonUint(fields, ".whir_rounds") - 1), suffix);
    }

    function _flipLastByte(string memory name) internal view returns (bytes memory m) {
        (uint256 offset, uint256 length) = _field(name);
        m = _copy(f1);
        m[offset + length - 1] ^= bytes1(uint8(1));
    }

    function test_f1_single_tx_accepts_with_the_v0_outputs() public {
        bytes memory v0Single = bytes.concat(v0Gkr, _slice(v0Whir, 976, v0Whir.length));
        bytes memory r0 = _accepts(proxyV0, v0Single);
        bytes memory r1 = _accepts(proxyF1, f1);
        require(r1.length == 96 && keccak256(r0) == keccak256(r1), "F1 outputs differ from v0");
    }

    function test_f1_rejects_mutated_gkr_round_pair() public {
        _accepts(proxyF1, f1);
        require(_rejects(proxyF1, _flipElement("gkr_dr_5_rounds", 0)), "b of a DR round");
        require(_rejects(proxyF1, _flipElement("gkr_dr_5_rounds", 1)), "c of a DR round");
        require(_rejects(proxyF1, _flipLastElement("gkr_layer_0_rounds")), "c of a circuit round");
    }

    function test_f1_rejects_mutated_evaluations_and_lines() public {
        require(_rejects(proxyF1, _flipLastElement("gkr_output_evals")), "output evaluation");
        require(_rejects(proxyF1, _flipLastElement("gkr_dr_5_lines")), "LSB line");
        require(_rejects(proxyF1, _flipLastElement("gkr_layer_0_evals")), "at-point evaluation");
    }

    function test_f1_rejects_mutated_whir_stream() public {
        require(_rejects(proxyF1, _flipElement("whir_0_sumcheck", 0)), "WHIR c0");
        require(_rejects(proxyF1, _flipLastElement(_finalRound("_sumcheck"))), "WHIR c2");
        require(_rejects(proxyF1, _flipLastElement(_finalRound("_monomials"))), "final monomial");
        require(_rejects(proxyF1, _flipLastElement("whir_0_query_0_memory_leaf")), "base leaf");
        require(_rejects(proxyF1, _flipLastElement("whir_1_query_0_leaf")), "intermediate leaf");
        require(_rejects(proxyF1, _flipLastByte("whir_1_cap")), "intermediate cap");
        require(_rejects(proxyF1, _flipLastByte("whir_1_ood")), "OOD value");
        require(_rejects(proxyF1, _flipLastByte(_finalRound("_pow_nonce"))), "WHIR PoW nonce");
    }

    function test_f1_rejects_mutated_sibling() public {
        require(_rejects(proxyF1, _flipLastByte("whir_1_query_0_path")), "intermediate sibling");
        require(_rejects(proxyF1, _flipLastByte("whir_0_query_0_setup_path")), "setup sibling");
    }

    function test_f1_rejects_non_canonical_lane() public {
        (uint256 offset,) = _field("gkr_output_evals");
        bytes memory m = _copy(f1);
        m[offset] = 0xff;
        m[offset + 1] = 0xff;
        require(_rejects(proxyF1, m), "GKR lane >= p");
        (offset,) = _field("whir_0_query_0_memory_leaf");
        m = _copy(f1);
        m[offset] = 0xff;
        m[offset + 1] = 0xff;
        require(_rejects(proxyF1, m), "WHIR lane >= p");
    }

    function test_f1_rejects_nonzero_pad_bit() public {
        require(_rejects(proxyF1, _flipLastByte("gkr_layer_0_evals")), "GKR run pad");
        require(_rejects(proxyF1, _flipLastByte("gkr_timestamps")), "timestamp run pad");
        require(_rejects(proxyF1, _flipLastByte("whir_0_query_0_memory_leaf")), "WHIR run pad");
    }

    function test_f1_rejects_truncated_extended_or_shifted_streams() public {
        require(_rejects(proxyF1, _slice(f1, 0, f1.length - 1)), "truncated");
        require(_rejects(proxyF1, bytes.concat(f1, hex"00")), "trailing byte");
        (uint256 offset, uint256 length) = _field("whir_1_query_0_path");
        bytes memory extra = bytes.concat(
            _slice(f1, 0, offset + length), _slice(f1, offset + length - 32, offset + length), _slice(f1, offset + length, f1.length)
        );
        require(_rejects(proxyF1, extra), "extra sibling");
        require(_rejects(proxyF1, _slice(f1, 0, gkrBytes)), "GKR section only");
    }

    function test_f1_rejects_swapped_tree_blocks() public {
        (uint256 mem, uint256 len) = _field("whir_0_query_0_memory_path");
        (uint256 setup, uint256 setupLen) = _field("whir_0_query_0_setup_path");
        if (setupLen < len) len = setupLen; // the setup path stops at the frontier
        bytes memory m = _copy(f1);
        for (uint256 i; i < len; ++i) {
            (m[mem + i], m[setup + i]) = (f1[setup + i], f1[mem + i]);
        }
        require(_rejects(proxyF1, m), "memory/setup paths swapped");
    }

    function test_f1_rejects_another_setup_frontier() public {
        _accepts(proxyF1, f1);
        bytes memory code = FRONTIER.code;
        code[code.length - 1] ^= 0x01;
        vm.etch(FRONTIER, code);
        require(_rejects(proxyF1, f1), "frontier code differs from the pinned hash");
    }

    /// Deployment check: the frontier data reduces to the proof's setup cap with the node function.
    function test_setup_frontier_reduces_to_the_setup_cap() public view {
        uint256 db = vm.parseJsonUint(fields, ".digest_bytes");
        uint256 level = vm.parseJsonUint(fields, ".setup_frontier_level");
        bytes memory code = FRONTIER.code;
        uint256 n = 1 << level;
        require(code.length == 1 + n * db && code[0] == 0x00, "frontier layout");
        bytes32 mask = bytes32(type(uint256).max << (8 * (32 - db)));
        bytes32[] memory nodes = new bytes32[](n);
        for (uint256 i; i < n; ++i) {
            bytes32 d;
            uint256 at = 33 + i * db; // +32 length word, +1 STOP
            assembly {
                d := mload(add(code, at))
            }
            nodes[i] = d & mask;
        }
        for (; n > 8; n /= 2) {
            for (uint256 i; i < n / 2; ++i) {
                nodes[i] = keccak256(abi.encodePacked(nodes[2 * i], nodes[2 * i + 1])) & mask;
            }
        }
        // v0 WHIR header: seed 32, batching 16, opening 16, z 25 × 16, memory cap 8 × 32, setup cap 8 × 32
        uint256 setupCap = 64 + 25 * 16 + 8 * 32;
        for (uint256 i; i < 8; ++i) {
            bytes32 c;
            uint256 at = 32 + setupCap + 32 * i;
            bytes memory whir = v0Whir;
            assembly {
                c := mload(add(whir, at))
            }
            require(nodes[i] == c, "frontier does not reduce to the setup cap");
        }
    }

    function test_f1_rejects_wrong_setup_cap() public {
        L1VerifierSingleTx wrong = new L1VerifierSingleTx(GKR_F1_WRONG_SETUP_CAP, WHIR_F1, gkrBytes);
        require(_rejects(wrong, f1), "verifier pinned to another setup cap");
    }

    function test_f1_rejects_altered_register_state() public {
        (uint256 offset,) = _field("gkr_timestamps");
        bytes memory m = _copy(f1);
        m[offset] ^= 0x80; // register 0 low timestamp limb, top bit
        require(_rejects(proxyF1, m), "register timestamp limb");
        (offset,) = _field("gkr_registers");
        m = _copy(f1);
        m[offset + 4 * 10] ^= 0x01; // x10 value
        require(_rejects(proxyF1, m), "register value");
        require(_rejects(proxyF1, _flipLastByte("gkr_top_bits")), "inits/teardowns top bits");
        require(_rejects(proxyF1, _flipLastByte("gkr_memory_cap")), "memory cap");
        require(_rejects(proxyF1, _flipLastByte("gkr_external_pow_nonce")), "external PoW nonce");
        require(_rejects(proxyF1, _flipLastByte("gkr_batching_pow_nonce")), "batching PoW nonce");
    }

    function test_f1_proxy_rejects_wrong_final_pc() public {
        L1VerifierSingleTx wrong = new L1VerifierSingleTx(GKR_F1_WRONG_PC, WHIR_F1, gkrBytes);
        require(_rejects(wrong, f1), "verifier with another final PC");
    }

    /// The F1 GKR verifier on the F1 GKR section returns exactly what the v0 single-tx GKR
    /// verifier returns on the v0 GKR calldata: preimage, commitment, public input, setup commitment.
    function test_f1_gkr_returns_the_v0_result() public {
        (bool ok0, bytes memory r0) = GKR_V0.call(v0Gkr);
        require(ok0, "v0 GKR must verify");
        (bool ok1, bytes memory r1) = GKR_F1.call(_slice(f1, 0, gkrBytes));
        require(ok1, "F1 GKR must verify");
        require(keccak256(r0) == keccak256(r1), "F1 GKR result differs from v0");
    }

    function test_f1_gkr_rejects_wrong_final_pc() public {
        (bool ok,) = GKR_F1_WRONG_PC.call(_slice(f1, 0, gkrBytes));
        require(!ok, "F1 GKR with another final PC must reject");
    }
}
