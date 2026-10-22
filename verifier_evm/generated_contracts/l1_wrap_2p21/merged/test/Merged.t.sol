// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

/// Single-transaction GKR+WHIR verification with the merged v0 `GkrWhirVerifier`: one call on
/// `merged_calldata.hex` (= GKR stream ‖ WHIR proof stream). The verifier hands the WHIR start
/// state over in memory and, on success, reports `(publicInput, auxInput, setupCommitment)` to
/// the registry it was constructed with. Rejection tests first accept the unmodified proof.
///   forge test -vv --match-contract MergedTest

import {GkrWhirVerifier} from "../src/GkrWhirVerifier.sol";
import {TestRegistry} from "../src/TestRegistry.sol";
import {MergedBase, RevertingRegistry} from "./MergedBase.sol";

contract MergedTest is MergedBase {
    // preimage layout (the generated __TEMPLATE_PREIMAGE_* constants): 32 registers x 12 B,
    // final pc/ts 12 B, 2 top-bits u32, then the setup cap (CAP x 32 B), then the memory cap
    uint256 constant SETUP_CAP_OFFSET = 32 * 12 + 12 + 2 * 4;
    uint256 constant CAP = 8;
    uint128 constant P = 0x7000000000000000000000000000001;

    event log_named_uint(string key, uint256 val);
    event log_named_bytes32(string key, bytes32 val);

    TestRegistry registry;
    GkrWhirVerifier verifier;
    bytes cd;
    string fields;
    uint256 gkrBytes;

    function setUp() public {
        registry = new TestRegistry();
        verifier = new GkrWhirVerifier(address(registry));
        cd = _hex(string.concat(DATA, "merged_calldata.hex"));
        fields = vm.readFile(string.concat(DATA, "calldata_fields.json"));
        gkrBytes = vm.parseJsonUint(fields, ".gkr_bytes");
    }

    // 8 registers' u32 values, each stored LE at calldata byte `reg*12`, concatenated.
    function _registers(bytes memory data, uint256 firstReg) internal pure returns (bytes32 out) {
        for (uint256 i = 0; i < 8; ++i) {
            uint256 off = (firstReg + i) * 12;
            for (uint256 b = 0; b < 4; ++b) {
                out |= bytes32(uint256(uint8(data[off + b])) << (8 * (31 - (i * 4 + b))));
            }
        }
    }

    // keccak256 of the setup cap: CAP digests, each 8 u32 words stored LE in the preimage and
    // hashed as BE words (the WHIR digest encoding).
    function _setupCommitment(bytes memory data) internal pure returns (bytes32) {
        bytes memory be = new bytes(CAP * 32);
        for (uint256 w = 0; w < CAP * 8; ++w) {
            for (uint256 b = 0; b < 4; ++b) {
                be[w * 4 + b] = data[SETUP_CAP_OFFSET + w * 4 + (3 - b)];
            }
        }
        return keccak256(be);
    }

    function _flipField(bytes memory payload, string memory key, uint256 width, string memory encoding)
        internal
        view
    {
        uint256 offset = vm.parseJsonUint(fields, string.concat(key, ".offset"));
        bytes memory expected = vm.parseJsonBytes(fields, string.concat(key, ".bytes"));
        require(
            keccak256(bytes(vm.parseJsonString(fields, string.concat(key, ".encoding")))) == keccak256(bytes(encoding)),
            "wrong field encoding"
        );
        require(expected.length == width && offset + width <= gkrBytes, "wrong field bounds");
        for (uint256 i; i < width; ++i) {
            require(payload[offset + i] == expected[i], "field differs from proof metadata");
        }
        payload[offset + width - 1] ^= bytes1(uint8(1));
    }

    function test_merged_single_tx() external {
        require(verifier.registry() == address(registry), "registry not pinned");
        emit log_named_uint("calldata_bytes", cd.length);
        uint256 g = gasleft();
        bytes memory ret = _accepts(address(verifier), cd);
        g -= gasleft();
        emit log_named_uint("verifier_call_gas", g);

        // the registry recorded exactly this verifier's mark
        require(registry.count() == 1, "expected exactly 1 mark");
        require(registry.lastVerifier() == address(verifier), "mark not from the verifier");
        (bytes32 publicInput, bytes32 auxInput, bytes32 setupCommitment) = registry.last();
        emit log_named_bytes32("public_input", publicInput);
        emit log_named_bytes32("aux_input", auxInput);
        emit log_named_bytes32("setup_commitment", setupCommitment);
        require(publicInput == _registers(cd, 10), "publicInput != registers x10..x17");
        require(auxInput == _registers(cd, 18), "auxInput != registers x18..x25");
        require(setupCommitment == _setupCommitment(cd), "setupCommitment != keccak(setup cap)");
        require(
            registry.isVerified(keccak256(abi.encode(publicInput, auxInput, setupCommitment))), "tuple not recorded"
        );
        // cross-check against the Rust-computed mark; the verifier returns the same tuple
        bytes memory expected = _hex(string.concat(DATA, "verified_mark.hex"));
        require(expected.length == 96 && keccak256(ret) == keccak256(expected), "return != Rust verified_mark");
        require(publicInput == _slice32(expected, 0), "publicInput != Rust verified_mark");
        require(auxInput == _slice32(expected, 32), "auxInput != Rust verified_mark");
        require(setupCommitment == _slice32(expected, 64), "setupCommitment != Rust verified_mark");
    }

    function test_runtime_size_fits_eip170() external {
        emit log_named_uint("runtime_bytes", address(verifier).code.length);
        require(address(verifier).code.length <= EIP170, "v0 verifier exceeds EIP-170");
    }

    /// A c0 lane of the first dimension-reducing round lifted by P is another 16-byte encoding of
    /// the same field element; the verifier rejects non-canonical encodings (never reduces them).
    function test_noncanonical_dim_reduce_lane_rejected() external {
        _accepts(address(verifier), cd);
        uint256 at = vm.parseJsonUint(fields, ".gkr.first_dim_reduce_round.offset");
        bytes memory round = vm.parseJsonBytes(fields, ".gkr.first_dim_reduce_round.bytes");
        require(keccak256(_slice(cd, at, at + 64)) == keccak256(round), "field differs from proof metadata");
        bytes memory bad = _copy(cd);
        uint128 c0 = uint128(uint256(_slice32(bad, at)) >> 128);
        require(c0 < P, "fixture lane is canonical");
        uint128 lifted = c0 + P; // < 2P < 2^128: same residue, non-canonical encoding
        for (uint256 b = 0; b < 16; ++b) {
            bad[at + b] = bytes1(uint8(lifted >> (8 * (15 - b))));
        }
        TestRegistry fresh = new TestRegistry();
        GkrWhirVerifier v = new GkrWhirVerifier(address(fresh));
        require(_rejects(address(v), bad), "a non-canonical coefficient lane must be rejected");
        require(fresh.count() == 0, "nothing may be marked");
    }

    function test_zero_registry_rejected() external {
        try new GkrWhirVerifier(address(0)) {
            revert("zero registry accepted");
        } catch {}
    }

    function test_codeless_registry_rejected() external {
        try new GkrWhirVerifier(address(0x1234)) {
            revert("code-less registry accepted");
        } catch {}
    }

    function test_refusing_registry_fails_verification() external {
        GkrWhirVerifier v = new GkrWhirVerifier(address(new RevertingRegistry()));
        require(_rejects(address(v), cd), "verification must fail when the registry refuses the mark");
    }

    function test_rejects_wrong_final_pc() external {
        _accepts(address(verifier), cd);
        address wrong = _deploy(
            "../negative/v0_wrong_final_pc/out/GkrWhirVerifier.sol/GkrWhirVerifier.json", address(registry)
        );
        require(_rejects(wrong, cd), "wrong expected final PC accepted");
    }

    function test_rejects_flipped_final_pc_transcript() external {
        _accepts(address(verifier), cd);
        bytes memory bad = _copy(cd);
        _flipField(bad, ".gkr.final_pc", 4, "u32_le");
        require(_rejects(address(verifier), bad), "changed final PC accepted");
    }

    function test_rejects_wrong_pow_nonce() external {
        _accepts(address(verifier), cd);
        bytes memory bad = _copy(cd);
        _flipField(bad, ".gkr.external_pow_nonce", 8, "u64_be");
        require(_rejects(address(verifier), bad), "changed external PoW nonce accepted");
    }

    function test_rejects_altered_inits_teardowns_top_bits() external {
        _accepts(address(verifier), cd);
        bytes memory bad = _copy(cd);
        bad[32 * 12 + 12] ^= 0x01; // top_bits[0], LE u32
        require(_rejects(address(verifier), bad), "changed inits/teardowns top bits accepted");
    }

    function test_rejects_tampered_gkr_bytes() external {
        _accepts(address(verifier), cd);
        uint256[3] memory at = [uint256(64), gkrBytes / 2, gkrBytes - 1];
        for (uint256 i; i < at.length; ++i) {
            bytes memory bad = _copy(cd);
            bad[at[i]] ^= bytes1(uint8(1));
            require(_rejects(address(verifier), bad), "tampered GKR byte accepted");
        }
    }

    /// WHIR stream bytes: first sumcheck coefficient, middle, and the last byte (final query path).
    function test_rejects_tampered_whir_bytes() external {
        _accepts(address(verifier), cd);
        uint256 g = gkrBytes;
        uint256[3] memory at = [g + 15, g + (cd.length - g) / 2, cd.length - 1];
        for (uint256 i; i < at.length; ++i) {
            bytes memory bad = _copy(cd);
            bad[at[i]] ^= bytes1(uint8(1));
            require(_rejects(address(verifier), bad), "tampered WHIR byte accepted");
        }
    }

    function test_rejects_truncated_or_extended() external {
        _accepts(address(verifier), cd);
        require(_rejects(address(verifier), _slice(cd, 0, cd.length - 1)), "truncated proof accepted");
        require(_rejects(address(verifier), bytes.concat(cd, hex"00")), "extended proof accepted");
        require(_rejects(address(verifier), _slice(cd, 0, gkrBytes)), "GKR half alone accepted");
    }

    /// This proof's GKR stream + the WHIR stream of another valid same-shape 2^21 proof.
    function test_rejects_mismatched_halves() external {
        _accepts(address(verifier), cd);
        bytes memory alt = _hex("./testdata/alt_whir_stream.hex");
        require(alt.length == cd.length - gkrBytes, "alt proof has another shape");
        require(keccak256(alt) != keccak256(_slice(cd, gkrBytes, cd.length)), "alt proof is this proof");
        require(_rejects(address(verifier), bytes.concat(_slice(cd, 0, gkrBytes), alt)), "mismatched halves accepted");
    }

    /// Every input that is not a valid proof reverts, including short inputs (registry() is the
    /// only ABI function and is not a proof).
    function test_rejects_selector_only_inputs() external {
        _accepts(address(verifier), cd);
        bytes4[3] memory sels = [bytes4(0xb969ce40), bytes4(0x08b39c85), bytes4(0)];
        for (uint256 i; i < sels.length; ++i) {
            require(_rejects(address(verifier), abi.encodePacked(sels[i])), "selector-only input accepted");
        }
        require(_rejects(address(verifier), ""), "empty input accepted");
    }
}
