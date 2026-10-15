// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// Single-transaction GKR+WHIR verification with the merged `GkrWhirVerifier`: one call on
/// `merged_calldata.hex` (= GKR stream ‖ WHIR proof stream). The verifier hands the WHIR start
/// state over in memory and, on success, reports `(publicInput, auxInput, setupCommitment)` to
/// the registry it was constructed with. The test checks the TestRegistry's record against
///  * the final registers in the calldata preimage (x10..x17 / x18..x25, LE u32 at byte reg*12)
///    and the keccak of the setup cap (LE u32 words at the preimage's setup-cap offset,
///    re-encoded BE) — derived from the calldata, so proof-agnostic;
///  * `verified_mark.hex`, the same tuple computed by the Rust `verified_mark` (cross-check of
///    the two encodings).
/// Plus the registry hardening: a zero / code-less registry is rejected at construction and a
/// registry that refuses the mark makes the verification transaction fail.
///
/// Prereq: `forge build` here (the verifier is compiled in this project).
///   forge test -vv                 (pure execution gas: --no-isolate)
///   forge test -vv --isolate       (tx-level gas incl. intrinsic + EIP-7623 floor)

import {GkrWhirVerifier, IVerificationRegistry} from "../src/GkrWhirVerifier.sol";
import {TestRegistry} from "../src/TestRegistry.sol";

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata s) external pure returns (bytes memory);
}

/// A registry that refuses every mark.
contract RevertingRegistry is IVerificationRegistry {
    function markVerified(bytes32, bytes32, bytes32) external pure override {
        revert("refused");
    }
}

contract GkrWhirMergedTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    // preimage layout (must match the generated __TEMPLATE_PREIMAGE_* constants): 32 registers
    // x 12 B, final pc/ts 12 B, 2 top-bits u32, then the setup cap (CAP x 32 B), then memory cap
    uint256 constant SETUP_CAP_OFFSET = 32 * 12 + 12 + 2 * 4;
    uint256 constant CAP = 8;

    event log_named_uint(string key, uint256 val);
    event log_named_bytes32(string key, bytes32 val);

    function _hex(string memory p) internal view returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", vm.readFile(p)));
    }

    // 8 registers' u32 values, each stored LE at calldata byte `reg*12`, concatenated.
    function _registers(bytes memory cd, uint256 firstReg) internal pure returns (bytes32 out) {
        for (uint256 i = 0; i < 8; ++i) {
            uint256 off = (firstReg + i) * 12;
            for (uint256 b = 0; b < 4; ++b) {
                out |= bytes32(uint256(uint8(cd[off + b])) << (8 * (31 - (i * 4 + b))));
            }
        }
    }

    // keccak256 of the setup cap: CAP digests, each 8 u32 words stored LE in the preimage and
    // hashed as BE words (the WHIR digest encoding).
    function _setupCommitment(bytes memory cd) internal pure returns (bytes32) {
        bytes memory be = new bytes(CAP * 32);
        for (uint256 w = 0; w < CAP * 8; ++w) {
            for (uint256 b = 0; b < 4; ++b) {
                be[w * 4 + b] = cd[SETUP_CAP_OFFSET + w * 4 + (3 - b)];
            }
        }
        return keccak256(be);
    }

    function _slice32(bytes memory b, uint256 off) internal pure returns (bytes32 out) {
        assembly ("memory-safe") { out := mload(add(add(b, 32), off)) }
    }

    function test_merged_single_tx() external {
        TestRegistry registry = new TestRegistry();
        GkrWhirVerifier v = new GkrWhirVerifier(address(registry));
        require(v.registry() == address(registry), "registry not pinned");
        bytes memory cd = _hex("../../debug_data/merged_calldata.hex");
        emit log_named_uint("calldata_bytes", cd.length);

        uint256 g = gasleft();
        (bool ok, bytes memory ret) = address(v).call(cd);
        g -= gasleft();
        require(ok, "merged verifier reverted");
        emit log_named_uint("verifier_call_gas", g);

        // the registry recorded exactly this verifier's mark
        require(registry.count() == 1, "expected exactly 1 mark");
        require(registry.lastVerifier() == address(v), "mark not from the verifier");
        (bytes32 publicInput, bytes32 auxInput, bytes32 setupCommitment) = registry.last();
        emit log_named_bytes32("public_input", publicInput);
        emit log_named_bytes32("aux_input", auxInput);
        emit log_named_bytes32("setup_commitment", setupCommitment);
        require(publicInput == _registers(cd, 10), "publicInput != registers x10..x17");
        require(auxInput == _registers(cd, 18), "auxInput != registers x18..x25");
        require(setupCommitment == _setupCommitment(cd), "setupCommitment != keccak(setup cap)");
        require(
            registry.isVerified(keccak256(abi.encode(publicInput, auxInput, setupCommitment))),
            "tuple not recorded"
        );
        // cross-check against the Rust-computed mark
        bytes memory expected = _hex("../../debug_data/verified_mark.hex");
        require(expected.length == 96, "verified_mark.hex must be 96 bytes");
        require(publicInput == _slice32(expected, 0), "publicInput != Rust verified_mark");
        require(auxInput == _slice32(expected, 32), "auxInput != Rust verified_mark");
        require(setupCommitment == _slice32(expected, 64), "setupCommitment != Rust verified_mark");
        // the verifier returns the same tuple
        require(ret.length == 96 && keccak256(ret) == keccak256(expected), "unexpected return data");
    }

    // The first dim-reduce round's [c0:16][c1:16] word sits right after preimage (916 B) + PoW
    // nonce (8 B) + output evals (10 * 16 * 16 B). A c0 lane lifted by P is a different
    // 16-byte encoding of the same field element: the transcript absorbs the reduced value and
    // every use reduces, so the proof must still verify with the same mark (before the
    // canonicalization fix in sumcheck_rounds the lifted lane made gkr_dr_final's wrapping
    // subtraction reject the honest claim).
    uint256 constant FIRST_DIM_REDUCE_ROUND_OFFSET = 916 + 8 + 10 * 16 * 16;
    uint128 constant P = 0x7000000000000000000000000000001;

    function test_noncanonical_dim_reduce_lane_is_canonicalized() external {
        TestRegistry registry = new TestRegistry();
        GkrWhirVerifier v = new GkrWhirVerifier(address(registry));
        bytes memory cd = _hex("../../debug_data/merged_calldata.hex");
        uint128 c0 = uint128(uint256(_slice32(cd, FIRST_DIM_REDUCE_ROUND_OFFSET)) >> 128);
        require(c0 < P, "fixture lane is canonical");
        uint128 lifted = c0 + P; // < 2P < 2^128
        for (uint256 b = 0; b < 16; ++b) {
            cd[FIRST_DIM_REDUCE_ROUND_OFFSET + b] = bytes1(uint8(lifted >> (8 * (15 - b))));
        }
        (bool ok, bytes memory ret) = address(v).call(cd);
        require(ok, "lifted (non-canonical) lane must verify as its residue");
        bytes memory expected = _hex("../../debug_data/verified_mark.hex");
        require(keccak256(ret) == keccak256(expected), "mark must be unchanged");
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
        bytes memory cd = _hex("../../debug_data/merged_calldata.hex");
        (bool ok,) = address(v).call(cd);
        require(!ok, "verification must fail when the registry refuses the mark");
    }
}
