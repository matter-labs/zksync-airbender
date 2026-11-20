// SPDX-License-Identifier: MIT
pragma solidity =0.8.38;

/// The L1 wrap proof, statement and malformed-input controls.
import {GkrWhirVerifierCode} from "../src/GkrWhirVerifier.sol";
import {TestRegistry} from "../src/TestRegistry.sol";
import {MergedBase, RevertingRegistry, AlternateRegistry} from "./MergedBase.sol";

contract MergedTest is MergedBase {
    string constant VERIFIER_ARTIFACT = "out/GkrWhirVerifier.sol/GkrWhirVerifier.json";

    event log_named_uint(string key, uint256 val);

    TestRegistry registry;
    address wrapVerifier;
    bytes proof;
    uint256 gkrBytes;
    string fields;

    function setUp() public {
        address pinnedRegistry = 0x78D549f2A140923c517c23b008DFfE979B3c4E91;
        vm.etch(pinnedRegistry, type(TestRegistry).runtimeCode);
        registry = TestRegistry(pinnedRegistry);
        wrapVerifier = _deploy(VERIFIER_ARTIFACT);
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

    /// The constructor returns this exact runtime prefix before appending setup.
    function _setupOffset() internal view returns (uint256) {
        return vm.parseJsonBytes(
            vm.readFile("out/GkrWhirVerifier.sol/GkrWhirVerifierCode.json"), ".deployedBytecode.object"
        )
        .length;
    }

    /// Absolute code offsets; the relative STOP/nodes/cap/table layout is unchanged.
    function _dataOffsets() internal view returns (uint256 cap, uint256 table) {
        uint256 db = vm.parseJsonUint(fields, ".digest_bytes");
        cap = _setupOffset() + 1 + (1 << vm.parseJsonUint(fields, ".setup_frontier_level")) * db;
        table = cap + 32 * 8;
    }

    function _flipLastByte(string memory name) internal view returns (bytes memory m) {
        (uint256 offset, uint256 length) = _field(name);
        m = _copy(proof);
        m[offset + length - 1] ^= bytes1(uint8(1));
    }

    function test_create_requires_glamsterdam_size_limit() external {
        bytes memory init = _creation(VERIFIER_ARTIFACT);
        require(init.length <= 131_072, "initcode exceeds Glamsterdam limit");
        address verifier;
        uint256 beforeCreate = gasleft();
        assembly ("memory-safe") {
            verifier := create(0, add(init, 32), mload(init))
        }
        uint256 deploymentGas = beforeCreate - gasleft();
        require(verifier != address(0), "plain CREATE failed");
        emit log_named_uint("runtime_bytes", verifier.code.length);
        emit log_named_uint("deployment_gas_amsterdam", deploymentGas);
        emit log_named_uint("initcode_bytes", init.length);
        require(verifier.code.length > EIP170, "Glamsterdam size dependency missing");
        require(verifier.code.length <= GLAMSTERDAM_CODE_LIMIT, "verifier exceeds EIP-7954");
        address wrong = _deploy("../negative/wrong_final_pc/out/GkrWhirVerifier.sol/GkrWhirVerifier.json");
        emit log_named_uint("negative_verifier_bytes", wrong.code.length);
        require(wrong.code.length <= GLAMSTERDAM_CODE_LIMIT, "negative verifier exceeds EIP-7954");
    }

    function test_registry_matches_deploy_create2_address() external view {
        address factory = 0xba5Ed099633D3B313e4D5F7bdc1305d3c28ba5Ed;
        bytes32 salt = 0x00000000000000000000000000000000000000000000000000616972621b0001;
        // CreateX _guard hashes this unpermissioned, non-redeploy-protected salt.
        bytes32 guardedSalt = keccak256(abi.encode(salt));
        address expected = address(
            uint160(
                uint256(
                    keccak256(
                        abi.encodePacked(hex"ff", factory, guardedSalt, keccak256(type(TestRegistry).creationCode))
                    )
                )
            )
        );
        require(address(registry) == expected, "registry differs from deploy.sh CREATE2 address");
    }

    function test_embedded_setup_matches_reference() external view {
        bytes memory code = wrapVerifier.code;
        require(
            keccak256(_slice(code, _setupOffset(), code.length))
                == 0x7024dc38fe6be11ae2b04cf75f6210dfdaeced21bde20b3e5836c01737528b85,
            "embedded setup bytes changed"
        );
        bytes memory prefix = type(GkrWhirVerifierCode).runtimeCode;
        require(code.length == prefix.length + 29_210, "runtime length differs");
        // Check every byte; the pinned setup hash above identifies the complete suffix.
        for (uint256 i; i < prefix.length; ++i) {
            require(code[i] == prefix[i], "runtime prefix differs");
        }
    }

    function test_merged_single_tx() external {
        bytes memory result = _accepts(wrapVerifier, proof);
        bytes memory expected = _hex(string.concat(DATA, "verified_mark.hex"));
        require(result.length == 64, "verifier return length");
        require(keccak256(result) == keccak256(expected), "verifier return != Rust verified_mark");
        require(registry.count() == 1 && registry.lastVerifier() == wrapVerifier, "mark not recorded");
        (bytes32 pi, bytes32 aux) = registry.last();
        require(keccak256(abi.encode(pi, aux)) == keccak256(expected), "recorded mark differs");
        require(registry.isVerified(keccak256(abi.encode(wrapVerifier, pi, aux))), "caller mark missing");
        require(!registry.isVerified(keccak256(abi.encode(address(this), pi, aux))), "other caller marked");
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
        require(_rejects(wrapVerifier, _flipLastByte("whir_0_query_0_memory_path")), "memory+witness sibling");
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
    }

    function _rejectsRunPad(string memory name) internal {
        (, uint256 length) = _field(name);
        uint256 elements = length * 8 / 123;
        uint256 pad = length * 8 - elements * 123;
        require(pad > 0 && pad < 8, "field map must describe a padded 123-bit run");
        require((elements * 123 + 7) / 8 == length, "run geometry differs");
        require(_rejects(wrapVerifier, _flipLastByte(name)), name);
    }

    function test_rejects_whir_sumcheck_pad() external {
        _rejectsRunPad("whir_0_sumcheck");
        _rejectsRunPad(_finalRound("_sumcheck")); // fold 5: ten fields, then five folding nonces
    }

    function test_rejects_setup_leaf_pad() external {
        _rejectsRunPad("whir_0_query_0_setup_leaf");
    }

    function test_rejects_gkr_round_pad() external {
        _rejectsRunPad("gkr_layer_0_rounds");
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

    /// Corrupt the embedded setup sections, without a separate data contract or hash check.
    function test_rejects_altered_setup_data() external {
        _accepts(wrapVerifier, proof);
        bytes memory code = wrapVerifier.code;
        (uint256 cap, uint256 table) = _dataOffsets();
        uint256 db = vm.parseJsonUint(fields, ".digest_bytes");
        bytes memory nodes = _copy(code);
        // Change every node so this control covers the proof's queried frontier entries.
        for (uint256 i = _setupOffset() + 1; i < cap; i += db) {
            nodes[i] ^= 0x01;
        }
        vm.etch(wrapVerifier, nodes);
        require(_rejects(wrapVerifier, proof), "altered embedded frontier accepted");
        uint256[2] memory at = [cap, table];
        for (uint256 i; i < at.length; ++i) {
            bytes memory m = _copy(code);
            m[at[i]] ^= 0x01;
            vm.etch(wrapVerifier, m);
            require(_rejects(wrapVerifier, proof), "altered embedded cap or table accepted");
        }
        vm.etch(wrapVerifier, code);
        _accepts(wrapVerifier, proof);
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
        address wrong = _deploy("../negative/wrong_final_pc/out/GkrWhirVerifier.sol/GkrWhirVerifier.json");
        require(_rejects(wrong, proof), "verifier with another final PC");
    }

    function test_rejects_external_pow() external {
        address control = _deploy("../negative/external_pow/out/GkrWhirVerifier.sol/GkrWhirVerifier.json");
        require(_rejects(control, proof), "external PoW check missing");
    }

    function test_rejects_batching_pow() external {
        address control = _deploy("../negative/batching_pow/out/GkrWhirVerifier.sol/GkrWhirVerifier.json");
        require(_rejects(control, proof), "batching PoW check missing");
    }

    function test_rejects_query_pow() external {
        uint256 rounds = vm.parseJsonUint(fields, ".whir_rounds");
        for (uint256 r; r < rounds; ++r) {
            address control = _deploy(string.concat(
                "../negative/query_pow_", vm.toString(r), "/out/GkrWhirVerifier.sol/GkrWhirVerifier.json"
            ));
            require(_rejects(control, proof), string.concat("query PoW check missing at round ", vm.toString(r)));
        }
    }

    function test_rejects_folding_pow() external {
        uint256 rounds = vm.parseJsonUint(fields, ".whir_rounds");
        for (uint256 r; r < rounds; ++r) {
            address control = _deploy(string.concat(
                "../negative/folding_pow_", vm.toString(r), "/out/GkrWhirVerifier.sol/GkrWhirVerifier.json"
            ));
            require(_rejects(control, proof), string.concat("folding PoW check missing at round ", vm.toString(r)));
        }
    }

    function test_rejects_ood_pow() external {
        uint256 rounds = vm.parseJsonUint(fields, ".whir_rounds");
        for (uint256 r; r + 1 < rounds; ++r) {
            address control = _deploy(string.concat(
                "../negative/ood_pow_", vm.toString(r), "/out/GkrWhirVerifier.sol/GkrWhirVerifier.json"
            ));
            require(_rejects(control, proof), string.concat("OOD PoW check missing at oracle ", vm.toString(r + 1)));
        }
    }

    function test_refusing_registry_fails_verification() external {
        vm.etch(address(registry), type(RevertingRegistry).runtimeCode);
        require(_rejects(wrapVerifier, proof), "refused registry mark accepted");
    }

    /// A suffix added after setup displaces the tail-relative start by one byte.
    function test_rejects_shifted_setup() external {
        _accepts(wrapVerifier, proof);
        bytes memory original = wrapVerifier.code;
        vm.etch(wrapVerifier, bytes.concat(original, hex"00"));
        require(_rejects(wrapVerifier, proof), "shifted setup accepted");
        vm.etch(wrapVerifier, original);
        _accepts(wrapVerifier, proof);
    }

    function test_rejects_selector_only_inputs() external {
        bytes4[4] memory selectors = [bytes4(0xb969ce40), bytes4(0x08b39c85), bytes4(0), bytes4(0x7b103999)];
        for (uint256 i; i < selectors.length; ++i) {
            require(_rejects(wrapVerifier, abi.encodePacked(selectors[i])), "selector-only input accepted");
        }
        require(_rejects(wrapVerifier, ""), "empty input accepted");
        bytes memory m = _copy(proof);
        m[0] = 0x7b;
        m[1] = 0x10;
        m[2] = 0x39;
        m[3] = 0x99;
        require(_rejects(wrapVerifier, m), "old registry selector followed by proof accepted");
    }

    function test_registry_implementation_can_be_replaced_at_generated_address() external {
        TestRegistry other = new TestRegistry();
        vm.etch(address(registry), type(AlternateRegistry).runtimeCode);
        AlternateRegistry replacement = AlternateRegistry(address(registry));
        bytes memory result = _accepts(wrapVerifier, proof);
        require(
            keccak256(result) == keccak256(_hex(string.concat(DATA, "verified_mark.hex"))),
            "statement with another registry implementation"
        );
        require(replacement.reporter() == wrapVerifier, "wrong registry caller");
        require(
            keccak256(abi.encode(replacement.publicInput(), replacement.auxInput())) == keccak256(result),
            "wrong registry statement"
        );
        require(other.count() == 0, "other address marked");
    }
}
