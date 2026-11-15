// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

/// The L1 wrap proof, statement and malformed-input controls.
import {GkrWhirVerifier} from "../src/GkrWhirVerifier.sol";
import {TestRegistry} from "../src/TestRegistry.sol";
import {MergedBase, RevertingRegistry} from "./MergedBase.sol";

contract MergedTest is MergedBase {
    string constant VERIFIER_ARTIFACT = "out/GkrWhirVerifier.sol/GkrWhirVerifier.json";

    event log_named_uint(string key, uint256 val);

    TestRegistry registry;
    address wrapVerifier;
    bytes proof;
    uint256 gkrBytes;
    string fields;

    function setUp() public {
        frontier = _deployFrontier();
        registry = new TestRegistry();
        wrapVerifier = _deploy(VERIFIER_ARTIFACT, address(registry));
        proof = _hex(string.concat(DATA, "single_tx_calldata.hex"));
        fields = vm.readFile(string.concat(DATA, "single_tx_calldata_fields.json"));
        gkrBytes = vm.parseJsonUint(fields, ".gkr_bytes");
        require(vm.parseJsonUint(fields, ".bytes") == proof.length, "calldata and field map disagree");
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
        m = _copy(proof);
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
        m = _copy(proof);
        m[offset + length - 1] ^= bytes1(uint8(1));
    }

    function test_runtime_size_fits_eip170() external {
        emit log_named_uint("runtime_bytes", wrapVerifier.code.length);
        require(wrapVerifier.code.length <= EIP170, "verifier exceeds EIP-170");
        emit log_named_uint("frontier_bytes", frontier.code.length);
        require(frontier.code.length <= EIP170, "setup data exceeds EIP-170");
        address wrong =
            _deploy("../negative/wrong_final_pc/out/GkrWhirVerifier.sol/GkrWhirVerifier.json", address(registry));
        emit log_named_uint("negative_verifier_bytes", wrong.code.length);
        require(wrong.code.length <= EIP170, "negative verifier exceeds EIP-170");
    }

    function test_merged_single_tx() external {
        bytes memory result = _accepts(wrapVerifier, proof);
        bytes memory expected = _hex(string.concat(DATA, "verified_mark.hex"));
        require(keccak256(result) == keccak256(expected), "verifier return != Rust verified_mark");
        require(registry.count() == 1 && registry.lastVerifier() == wrapVerifier, "mark not recorded");
        (bytes32 pi, bytes32 aux, bytes32 sc) = registry.last();
        require(keccak256(abi.encode(pi, aux, sc)) == keccak256(expected), "recorded mark differs");
        (uint256 registers,) = _field("gkr_registers");
        require(pi == _slice32(proof, registers + 10 * 4), "public input != x10..x17");
        require(aux == _slice32(proof, registers + 18 * 4), "aux input != x18..x25");
    }

    function test_rejects_mutated_gkr_round_pair() external {
        _accepts(wrapVerifier, proof);
        require(_rejects(wrapVerifier, _flipElement("gkr_dr_5_rounds", 0)), "b of a DR round");
        require(_rejects(wrapVerifier, _flipElement("gkr_dr_5_rounds", 1)), "c of a DR round");
        require(_rejects(wrapVerifier, _flipLastElement("gkr_layer_0_rounds")), "c of a circuit round");
    }

    function test_rejects_mutated_evaluations_and_lines() external {
        require(_rejects(wrapVerifier, _flipLastElement("gkr_output_evals")), "output evaluation");
        require(_rejects(wrapVerifier, _flipLastElement("gkr_dr_5_lines")), "LSB line");
        require(_rejects(wrapVerifier, _flipLastElement("gkr_layer_0_evals")), "at-point evaluation");
    }

    function test_rejects_mutated_whir_stream() external {
        require(_rejects(wrapVerifier, _flipElement("whir_0_sumcheck", 0)), "WHIR c0");
        require(_rejects(wrapVerifier, _flipLastElement(_finalRound("_sumcheck"))), "WHIR c2");
        require(_rejects(wrapVerifier, _flipLastElement(_finalRound("_monomials"))), "final monomial");
        require(_rejects(wrapVerifier, _flipLastElement("whir_0_query_0_memory_leaf")), "base leaf");
        require(_rejects(wrapVerifier, _flipLastElement("whir_1_query_0_leaf")), "intermediate leaf");
        require(_rejects(wrapVerifier, _flipLastByte("whir_1_cap")), "intermediate cap");
        require(_rejects(wrapVerifier, _flipLastByte("whir_1_ood")), "OOD value");
        require(_rejects(wrapVerifier, _flipLastByte(_finalRound("_pow_nonce"))), "WHIR PoW nonce");
    }

    function test_rejects_mutated_sibling() external {
        require(_rejects(wrapVerifier, _flipLastByte("whir_1_query_0_path")), "intermediate sibling");
        require(_rejects(wrapVerifier, _flipLastByte("whir_0_query_0_setup_path")), "setup sibling");
    }

    function test_rejects_non_canonical_lane() external {
        (uint256 offset,) = _field("gkr_output_evals");
        bytes memory m = _copy(proof);
        m[offset] = 0xff;
        m[offset + 1] = 0xff;
        require(_rejects(wrapVerifier, m), "GKR lane >= p");
        (offset,) = _field("whir_0_query_0_memory_leaf");
        m = _copy(proof);
        m[offset] = 0xff;
        m[offset + 1] = 0xff;
        require(_rejects(wrapVerifier, m), "WHIR lane >= p");
    }

    function test_rejects_nonzero_pad_bit() external {
        require(_rejects(wrapVerifier, _flipLastByte("gkr_layer_0_evals")), "GKR run pad");
        require(_rejects(wrapVerifier, _flipLastByte("gkr_timestamps")), "timestamp run pad");
        require(_rejects(wrapVerifier, _flipLastByte("whir_0_query_0_memory_leaf")), "WHIR run pad");
    }

    function test_rejects_truncated_extended_or_shifted_streams() external {
        _accepts(wrapVerifier, proof);
        require(_rejects(wrapVerifier, _slice(proof, 0, proof.length - 1)), "truncated");
        require(_rejects(wrapVerifier, bytes.concat(proof, hex"00")), "trailing byte");
        (uint256 offset, uint256 length) = _field("whir_1_query_0_path");
        bytes memory extra = bytes.concat(
            _slice(proof, 0, offset + length),
            _slice(proof, offset + length - 32, offset + length),
            _slice(proof, offset + length, proof.length)
        );
        require(_rejects(wrapVerifier, extra), "extra sibling");
        require(_rejects(wrapVerifier, _slice(proof, 0, gkrBytes)), "GKR section only");
        require(_rejects(wrapVerifier, ""), "empty input");
    }

    function test_rejects_swapped_tree_blocks() external {
        (uint256 mem, uint256 len) = _field("whir_0_query_0_memory_path");
        (uint256 setup, uint256 setupLen) = _field("whir_0_query_0_setup_path");
        if (setupLen < len) len = setupLen; // the setup path stops at the frontier
        bytes memory m = _copy(proof);
        for (uint256 i; i < len; ++i) {
            (m[mem + i], m[setup + i]) = (proof[setup + i], proof[mem + i]);
        }
        require(_rejects(wrapVerifier, m), "memory/setup paths swapped");
    }

    /// Every section of the setup data (frontier, setup cap image, GKR term table) is covered by
    /// the pinned code hash, and the data contract must exist.
    function test_rejects_altered_setup_data() external {
        _accepts(wrapVerifier, proof);
        bytes memory code = frontier.code;
        (uint256 cap, uint256 table) = _dataOffsets();
        uint256[4] memory at = [uint256(1), cap, table, code.length - 1];
        for (uint256 i; i < at.length; ++i) {
            bytes memory m = _copy(code);
            m[at[i]] ^= 0x01;
            vm.etch(frontier, m);
            require(_rejects(wrapVerifier, proof), "setup data differs from the pinned hash");
        }
        vm.etch(frontier, "");
        require(_rejects(wrapVerifier, proof), "no setup data contract");
    }

    /// A verifier re-pinned to altered setup data rejects the proof: the setup cap and the GKR
    /// term table are read, not only hashed.
    function test_rejects_repinned_wrong_setup_data() external {
        bytes memory code = frontier.code;
        bytes memory verifier = wrapVerifier.code;
        bytes32 pinned = keccak256(code);
        vm.etch(wrapVerifier, _repin(verifier, pinned, pinned));
        _accepts(wrapVerifier, proof);
        (uint256 cap, uint256 table) = _dataOffsets();
        uint256[2] memory at = [cap, table];
        for (uint256 i; i < at.length; ++i) {
            bytes memory m = _copy(code);
            m[at[i]] ^= 0x01;
            vm.etch(frontier, m);
            vm.etch(wrapVerifier, _repin(verifier, pinned, keccak256(m)));
            require(_rejects(wrapVerifier, proof), "verifier pinned to altered setup data");
        }
    }

    function test_rejects_altered_register_state() external {
        (uint256 offset,) = _field("gkr_timestamps");
        bytes memory m = _copy(proof);
        m[offset] ^= 0x80; // register 0 low timestamp limb, top bit
        require(_rejects(wrapVerifier, m), "register timestamp limb");
        (offset,) = _field("gkr_registers");
        m = _copy(proof);
        m[offset + 4 * 10] ^= 0x01; // x10 value
        require(_rejects(wrapVerifier, m), "register value");
        require(_rejects(wrapVerifier, _flipLastByte("gkr_memory_cap")), "memory cap");
        require(_rejects(wrapVerifier, _flipLastByte("gkr_external_pow_nonce")), "external PoW nonce");
        require(_rejects(wrapVerifier, _flipLastByte("gkr_batching_pow_nonce")), "batching PoW nonce");
    }

    function test_rejects_wrong_final_pc() external {
        address wrong =
            _deploy("../negative/wrong_final_pc/out/GkrWhirVerifier.sol/GkrWhirVerifier.json", address(registry));
        require(_rejects(wrong, proof), "verifier with another final PC");
    }

    function test_registry_constructor_rejections() external {
        for (uint256 i; i < 2; ++i) {
            address bad = i == 0 ? address(0) : address(0x1234);
            try new GkrWhirVerifier(bad, frontier) {
                revert("invalid registry accepted");
            } catch Error(string memory reason) {
                require(
                    keccak256(bytes(reason)) == keccak256(bytes(i == 0 ? "registry is zero" : "registry has no code")),
                    "wrong rejection"
                );
            }
        }
    }

    function test_refusing_registry_fails_verification() external {
        GkrWhirVerifier verifier = new GkrWhirVerifier(address(new RevertingRegistry()), frontier);
        require(_rejects(address(verifier), proof), "refused registry mark accepted");
    }

    function test_rejects_selector_only_inputs() external {
        bytes4[3] memory selectors = [bytes4(0xb969ce40), bytes4(0x08b39c85), bytes4(0)];
        for (uint256 i; i < selectors.length; ++i) {
            require(_rejects(wrapVerifier, abi.encodePacked(selectors[i])), "selector-only input accepted");
        }
        require(_rejects(wrapVerifier, ""), "empty input accepted");
    }

    function test_frontier_constructor_rejects_wrong_code() external {
        address[2] memory bad = [address(0), address(registry)];
        for (uint256 i; i < bad.length; ++i) {
            try new GkrWhirVerifier(address(registry), bad[i]) {
                revert("wrong setup code accepted");
            } catch Error(string memory reason) {
                require(keccak256(bytes(reason)) == keccak256("setup frontier code hash"), "wrong rejection");
            }
        }
    }

    function test_frontier_address_is_a_constructor_input() external {
        address other = _deployFrontier();
        GkrWhirVerifier verifier = new GkrWhirVerifier(address(registry), other);
        bytes memory result = _accepts(address(verifier), proof);
        require(
            keccak256(result) == keccak256(_hex(string.concat(DATA, "verified_mark.hex"))),
            "statement at another data address"
        );
    }
}
