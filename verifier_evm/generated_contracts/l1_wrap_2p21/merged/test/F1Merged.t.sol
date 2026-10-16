// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

/// Format F1 (verifier_evm::encoding) on the merged F1 `GkrWhirVerifier` (`../merged_f1`) and its
/// setup data contract, against the merged v0 verifier on the same proof. The F1 runtime is
/// checked against EIP-170 by `test_f1_runtime_size_fits_eip170`.
///   forge test -vv --match-contract F1MergedTest

import {GkrWhirVerifier} from "../src/GkrWhirVerifier.sol";
import {TestRegistry} from "../src/TestRegistry.sol";
import {MergedBase} from "./MergedBase.sol";

contract F1MergedTest is MergedBase {
    string constant F1_ARTIFACT = "../merged_f1/out/GkrWhirVerifier.sol/GkrWhirVerifier.json";

    event log_named_uint(string key, uint256 val);

    TestRegistry registry;
    address v0;
    address f1v;
    bytes v0cd;
    bytes f1;
    uint256 gkrBytes;
    string fields;

    function setUp() public {
        _placeFrontier();
        registry = new TestRegistry();
        v0 = address(new GkrWhirVerifier(address(registry)));
        f1v = _deploy(F1_ARTIFACT, address(registry));
        v0cd = _hex(string.concat(DATA, "merged_calldata.hex"));
        f1 = _hex(string.concat(DATA, "single_tx_f1.hex"));
        fields = vm.readFile(string.concat(DATA, "single_tx_f1_fields.json"));
        gkrBytes = vm.parseJsonUint(fields, ".gkr_bytes");
        require(vm.parseJsonUint(fields, ".bytes") == f1.length, "F1 calldata and field map disagree");
    }

    function _field(string memory name) internal view returns (uint256 offset, uint256 length) {
        offset = vm.parseJsonUint(fields, string.concat(".fields.", name, ".offset"));
        length = vm.parseJsonUint(fields, string.concat(".fields.", name, ".length"));
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

    /// Code offsets of the setup cap image and the GKR term table in the setup data contract.
    function _dataOffsets() internal view returns (uint256 cap, uint256 table) {
        uint256 db = vm.parseJsonUint(fields, ".digest_bytes");
        cap = 1 + (1 << vm.parseJsonUint(fields, ".setup_frontier_level")) * db;
        table = cap + 32 * 8;
    }

    /// `code` with the pinned setup data hash `from` re-pinned to `to`: the one PUSH32 operand (at
    /// an instruction boundary) holding the hash or its negation (the optimizer compares by adding
    /// −hash).
    function _repin(bytes memory code, bytes32 from, bytes32 to) internal pure returns (bytes memory out) {
        out = _copy(code);
        uint256 n;
        for (uint256 i; i < out.length; ++i) {
            uint8 op = uint8(out[i]);
            if (op < 0x60 || op > 0x7f) continue;
            if (op == 0x7f && i + 33 <= out.length) {
                bytes32 w = _slice32(out, i + 1);
                bytes32 v;
                bool hit = true;
                unchecked {
                    if (w == from) v = to;
                    else if (uint256(w) == 0 - uint256(from)) v = bytes32(0 - uint256(to));
                    else hit = false;
                }
                if (hit) {
                    assembly ("memory-safe") {
                        mstore(add(add(out, 33), i), v)
                    }
                    ++n;
                }
            }
            i += op - 0x5f;
        }
        require(n == 1, "the pinned setup data hash must be one PUSH32 operand");
    }

    function _flipLastByte(string memory name) internal view returns (bytes memory m) {
        (uint256 offset, uint256 length) = _field(name);
        m = _copy(f1);
        m[offset + length - 1] ^= bytes1(uint8(1));
    }

    function test_f1_runtime_size_fits_eip170() external {
        emit log_named_uint("runtime_bytes", f1v.code.length);
        require(f1v.code.length <= EIP170, "F1 verifier exceeds EIP-170");
    }

    /// Same statement as v0 and the Rust mark, reported to the registry and returned.
    function test_f1_accepts_with_the_v0_outputs() external {
        emit log_named_uint("calldata_bytes", f1.length);
        bytes memory r0 = _accepts(v0, v0cd);
        uint256 g = gasleft();
        bytes memory r1 = _accepts(f1v, f1);
        g -= gasleft();
        emit log_named_uint("verifier_call_gas", g);
        bytes memory expected = _hex(string.concat(DATA, "verified_mark.hex"));
        require(keccak256(r0) == keccak256(expected), "v0 return != Rust verified_mark");
        require(keccak256(r1) == keccak256(expected), "F1 return != Rust verified_mark");
        require(registry.count() == 2 && registry.lastVerifier() == f1v, "F1 mark not recorded");
        (bytes32 pi, bytes32 aux, bytes32 sc) = registry.last();
        require(keccak256(abi.encode(pi, aux, sc)) == keccak256(expected), "F1 mark differs");
    }

    function test_f1_rejects_mutated_gkr_round_pair() external {
        _accepts(f1v, f1);
        require(_rejects(f1v, _flipElement("gkr_dr_5_rounds", 0)), "b of a DR round");
        require(_rejects(f1v, _flipElement("gkr_dr_5_rounds", 1)), "c of a DR round");
        require(_rejects(f1v, _flipLastElement("gkr_layer_0_rounds")), "c of a circuit round");
    }

    function test_f1_rejects_mutated_evaluations_and_lines() external {
        require(_rejects(f1v, _flipLastElement("gkr_output_evals")), "output evaluation");
        require(_rejects(f1v, _flipLastElement("gkr_dr_5_lines")), "LSB line");
        require(_rejects(f1v, _flipLastElement("gkr_layer_0_evals")), "at-point evaluation");
    }

    function test_f1_rejects_mutated_whir_stream() external {
        require(_rejects(f1v, _flipElement("whir_0_sumcheck", 0)), "WHIR c0");
        require(_rejects(f1v, _flipLastElement(_finalRound("_sumcheck"))), "WHIR c2");
        require(_rejects(f1v, _flipLastElement(_finalRound("_monomials"))), "final monomial");
        require(_rejects(f1v, _flipLastElement("whir_0_query_0_memory_leaf")), "base leaf");
        require(_rejects(f1v, _flipLastElement("whir_1_query_0_leaf")), "intermediate leaf");
        require(_rejects(f1v, _flipLastByte("whir_1_cap")), "intermediate cap");
        require(_rejects(f1v, _flipLastByte("whir_1_ood")), "OOD value");
        require(_rejects(f1v, _flipLastByte(_finalRound("_pow_nonce"))), "WHIR PoW nonce");
    }

    function test_f1_rejects_mutated_sibling() external {
        require(_rejects(f1v, _flipLastByte("whir_1_query_0_path")), "intermediate sibling");
        require(_rejects(f1v, _flipLastByte("whir_0_query_0_setup_path")), "setup sibling");
    }

    function test_f1_rejects_non_canonical_lane() external {
        (uint256 offset,) = _field("gkr_output_evals");
        bytes memory m = _copy(f1);
        m[offset] = 0xff;
        m[offset + 1] = 0xff;
        require(_rejects(f1v, m), "GKR lane >= p");
        (offset,) = _field("whir_0_query_0_memory_leaf");
        m = _copy(f1);
        m[offset] = 0xff;
        m[offset + 1] = 0xff;
        require(_rejects(f1v, m), "WHIR lane >= p");
    }

    function test_f1_rejects_nonzero_pad_bit() external {
        require(_rejects(f1v, _flipLastByte("gkr_layer_0_evals")), "GKR run pad");
        require(_rejects(f1v, _flipLastByte("gkr_timestamps")), "timestamp run pad");
        require(_rejects(f1v, _flipLastByte("whir_0_query_0_memory_leaf")), "WHIR run pad");
    }

    function test_f1_rejects_truncated_extended_or_shifted_streams() external {
        _accepts(f1v, f1);
        require(_rejects(f1v, _slice(f1, 0, f1.length - 1)), "truncated");
        require(_rejects(f1v, bytes.concat(f1, hex"00")), "trailing byte");
        (uint256 offset, uint256 length) = _field("whir_1_query_0_path");
        bytes memory extra = bytes.concat(
            _slice(f1, 0, offset + length),
            _slice(f1, offset + length - 32, offset + length),
            _slice(f1, offset + length, f1.length)
        );
        require(_rejects(f1v, extra), "extra sibling");
        require(_rejects(f1v, _slice(f1, 0, gkrBytes)), "GKR section only");
        require(_rejects(f1v, ""), "empty input");
    }

    function test_f1_rejects_swapped_tree_blocks() external {
        (uint256 mem, uint256 len) = _field("whir_0_query_0_memory_path");
        (uint256 setup, uint256 setupLen) = _field("whir_0_query_0_setup_path");
        if (setupLen < len) len = setupLen; // the setup path stops at the frontier
        bytes memory m = _copy(f1);
        for (uint256 i; i < len; ++i) {
            (m[mem + i], m[setup + i]) = (f1[setup + i], f1[mem + i]);
        }
        require(_rejects(f1v, m), "memory/setup paths swapped");
    }

    /// Every section of the setup data (frontier, setup cap image, GKR term table) is covered by
    /// the pinned code hash, and the data contract must exist.
    function test_f1_rejects_altered_setup_data() external {
        _accepts(f1v, f1);
        bytes memory code = FRONTIER.code;
        (uint256 cap, uint256 table) = _dataOffsets();
        uint256[4] memory at = [uint256(1), cap, table, code.length - 1];
        for (uint256 i; i < at.length; ++i) {
            bytes memory m = _copy(code);
            m[at[i]] ^= 0x01;
            vm.etch(FRONTIER, m);
            require(_rejects(f1v, f1), "setup data differs from the pinned hash");
        }
        vm.etch(FRONTIER, "");
        require(_rejects(f1v, f1), "no setup data contract");
    }

    /// A verifier re-pinned to altered setup data rejects the proof: the setup cap and the GKR
    /// term table are read, not only hashed.
    function test_f1_rejects_repinned_wrong_setup_data() external {
        bytes memory code = FRONTIER.code;
        bytes memory verifier = f1v.code;
        bytes32 pinned = keccak256(code);
        vm.etch(f1v, _repin(verifier, pinned, pinned));
        _accepts(f1v, f1);
        (uint256 cap, uint256 table) = _dataOffsets();
        uint256[2] memory at = [cap, table];
        for (uint256 i; i < at.length; ++i) {
            bytes memory m = _copy(code);
            m[at[i]] ^= 0x01;
            vm.etch(FRONTIER, m);
            vm.etch(f1v, _repin(verifier, pinned, keccak256(m)));
            require(_rejects(f1v, f1), "verifier pinned to altered setup data");
        }
    }

    /// Deployment check: the frontier reduces to the proof's setup cap (LE u32 words in the v0
    /// preimage at the setup-cap offset) with the node function, and the data's setup cap image
    /// is those preimage bytes.
    function test_setup_frontier_reduces_to_the_setup_cap() external view {
        uint256 db = vm.parseJsonUint(fields, ".digest_bytes");
        uint256 level = vm.parseJsonUint(fields, ".setup_frontier_level");
        bytes memory code = FRONTIER.code;
        uint256 n = 1 << level;
        (uint256 capAt, uint256 table) = _dataOffsets();
        require(code.length > table && code[0] == 0x00, "setup data layout");
        bytes32 mask = bytes32(type(uint256).max << (8 * (32 - db)));
        bytes32[] memory nodes = new bytes32[](n);
        for (uint256 i; i < n; ++i) {
            nodes[i] = _slice32(code, 1 + i * db) & mask;
        }
        for (; n > 8; n /= 2) {
            for (uint256 i; i < n / 2; ++i) {
                nodes[i] = keccak256(abi.encodePacked(nodes[2 * i], nodes[2 * i + 1])) & mask;
            }
        }
        uint256 setupCap = 32 * 12 + 12 + 2 * 4;
        for (uint256 i; i < 8; ++i) {
            bytes memory be = new bytes(32);
            for (uint256 w; w < 8; ++w) {
                for (uint256 b; b < 4; ++b) {
                    be[w * 4 + b] = v0cd[setupCap + 32 * i + w * 4 + (3 - b)];
                }
            }
            require(nodes[i] == bytes32(be), "frontier does not reduce to the setup cap");
        }
        require(
            keccak256(_slice(code, capAt, table)) == keccak256(_slice(v0cd, setupCap, setupCap + 32 * 8)),
            "setup cap image"
        );
    }

    /// E8 control: a verifier pinned to another setup (one frontier node and the cap it reduces
    /// to), with its own setup data in place.
    function test_f1_rejects_wrong_setup_cap() external {
        _placeFrontier("../negative/f1_wrong_setup_cap");
        address wrong = _deploy(
            "../negative/f1_wrong_setup_cap/out/GkrWhirVerifier.sol/GkrWhirVerifier.json", address(registry)
        );
        require(_rejects(wrong, f1), "verifier pinned to another setup");
    }

    /// The F1 render without a setup frontier (setup paths to the cap) accepts its own calldata
    /// with the v0 statement.
    function test_f1_cap_level_control_accepts() external {
        _placeFrontier("../controls/f1_cap_level");
        address control = _deploy(
            "../controls/f1_cap_level/out/GkrWhirVerifier.sol/GkrWhirVerifier.json", address(registry)
        );
        bytes memory r0 = _accepts(v0, v0cd);
        bytes memory r1 = _accepts(control, _hex(string.concat(DATA, "single_tx_f1_cap_level.hex")));
        require(keccak256(r0) == keccak256(r1), "control statement differs from v0");
    }

    function test_f1_rejects_altered_register_state() external {
        (uint256 offset,) = _field("gkr_timestamps");
        bytes memory m = _copy(f1);
        m[offset] ^= 0x80; // register 0 low timestamp limb, top bit
        require(_rejects(f1v, m), "register timestamp limb");
        (offset,) = _field("gkr_registers");
        m = _copy(f1);
        m[offset + 4 * 10] ^= 0x01; // x10 value
        require(_rejects(f1v, m), "register value");
        require(_rejects(f1v, _flipLastByte("gkr_top_bits")), "inits/teardowns top bits");
        require(_rejects(f1v, _flipLastByte("gkr_memory_cap")), "memory cap");
        require(_rejects(f1v, _flipLastByte("gkr_external_pow_nonce")), "external PoW nonce");
        require(_rejects(f1v, _flipLastByte("gkr_batching_pow_nonce")), "batching PoW nonce");
    }

    function test_f1_rejects_wrong_final_pc() external {
        address wrong = _deploy(
            "../negative/f1_wrong_final_pc/out/GkrWhirVerifier.sol/GkrWhirVerifier.json", address(registry)
        );
        require(_rejects(wrong, f1), "verifier with another final PC");
    }

    /// The F1 GKR section followed by the v0 WHIR stream (and vice versa) is not a proof.
    function test_f1_rejects_mixed_formats() external {
        uint256 v0Gkr = vm.parseJsonUint(vm.readFile(string.concat(DATA, "calldata_fields.json")), ".gkr_bytes");
        require(_rejects(f1v, bytes.concat(_slice(f1, 0, gkrBytes), _slice(v0cd, v0Gkr, v0cd.length))), "F1 GKR + v0 WHIR");
        require(_rejects(v0, bytes.concat(_slice(v0cd, 0, v0Gkr), _slice(f1, gkrBytes, f1.length))), "v0 GKR + F1 WHIR");
    }
}
