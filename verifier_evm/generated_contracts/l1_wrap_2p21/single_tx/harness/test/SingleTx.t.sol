// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

import {L1VerifierSingleTx} from "../src/L1VerifierSingleTx.sol";
import {GkrWhirRegistry} from "two_tx/src/GkrWhirRegistry.sol";

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

/// Returns a well-formed WHIR result whose commitment differs from any real one.
contract WrongCommitmentWhir {
    fallback() external {
        assembly {
            mstore(96, 1)
            return(0, 128)
        }
    }
}

/// Single-tx proxy over the 2p21 verifiers. Rejection tests first accept the unmodified proof.
contract SingleTxTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    address constant GKR = address(uint160(0x611b0002));
    address constant GKR_WRONG_PC = address(uint160(0x611b0003));
    address constant WHIR = address(uint160(0x11170002));
    address constant REGISTRY = address(uint160(0xCAFE0001)); // two-tx verifiers' registry constant
    address constant GKR_TWO_TX = address(uint160(0x611b0001));
    address constant WHIR_TWO_TX = address(uint160(0x11170001));
    string constant DATA = "../../../../debug_data/l1_wrap_2p21/";
    bytes gkrCalldata;
    bytes whirCalldata;
    bytes single;
    uint256 plen;
    string fields;
    L1VerifierSingleTx verifier;

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
        vm.etch(GKR, _deployed("../gkr/out/GkrVerifier.sol/GKRVerifier.json"));
        vm.etch(GKR_WRONG_PC, _deployed("../gkr_negative/out/GkrVerifierWrongFinalPc.sol/GKRVerifier.json"));
        vm.etch(WHIR, _deployed("../whir/out/WhirVerifier.sol/WhirVerifier.json"));
        gkrCalldata = _calldata(string.concat(DATA, "gkr_full_calldata.hex"));
        whirCalldata = _calldata(string.concat(DATA, "proth120_whir_calldata_from_proof.hex"));
        fields = vm.readFile(string.concat(DATA, "calldata_fields.json"));
        // The single-tx GKR returns [preimage][commitment][public_input][setup_commitment]; the
        // preimage must be byte-identical to the two-tx WHIR calldata prefix it replaces.
        (bool ok, bytes memory ret) = GKR.call(gkrCalldata);
        require(ok, "single-tx GKR must verify the unmodified proof");
        require(ret.length > 96, "GKR returned no preimage");
        plen = ret.length - 96;
        require(keccak256(_slice(ret, 0, plen)) == keccak256(_slice(whirCalldata, 0, plen)), "preimage differs");
        single = bytes.concat(gkrCalldata, _slice(whirCalldata, plen, whirCalldata.length));
        verifier = new L1VerifierSingleTx(GKR, WHIR, gkrCalldata.length);
    }

    function _accept(L1VerifierSingleTx v, bytes memory data)
        internal
        returns (bytes32 commitment, bytes32 publicInput, bytes32 setupCommitment)
    {
        (bool ok, bytes memory ret) = address(v).call(data);
        require(ok, "unmodified single-tx proof must verify");
        (commitment, publicInput, setupCommitment) = abi.decode(ret, (bytes32, bytes32, bytes32));
    }

    function _rejects(L1VerifierSingleTx v, bytes memory data) internal returns (bool) {
        (bool ok,) = address(v).call(data);
        return !ok;
    }

    function _flipField(bytes memory payload, string memory key, uint256 width, string memory encoding) internal view {
        uint256 offset = vm.parseJsonUint(fields, string.concat(key, ".offset"));
        bytes memory expected = vm.parseJsonBytes(fields, string.concat(key, ".bytes"));
        require(
            keccak256(bytes(vm.parseJsonString(fields, string.concat(key, ".encoding")))) == keccak256(bytes(encoding)),
            "wrong field encoding"
        );
        require(expected.length == width && offset + width <= gkrCalldata.length, "wrong field bounds");
        for (uint256 i; i < width; ++i) {
            require(payload[offset + i] == expected[i], "field differs from proof metadata");
        }
        payload[offset + width - 1] ^= bytes1(uint8(1));
    }

    function test_single_tx_accepts() public {
        (bytes32 commitment,,) = _accept(verifier, single);
        require(commitment == keccak256(_slice(whirCalldata, 0, plen)), "wrong committed state");
        require(single.length == gkrCalldata.length + whirCalldata.length - plen, "wrong calldata length");
    }

    /// Same verdict and public data as the two-tx registry pair on the same proof.
    function test_matches_two_tx_registry() public {
        GkrWhirRegistry impl = new GkrWhirRegistry(address(this));
        vm.etch(REGISTRY, address(impl).code);
        vm.etch(GKR_TWO_TX, _deployed("../../gkr/out/GkrVerifier.sol/GKRVerifier.json"));
        vm.etch(WHIR_TWO_TX, _deployed("../../whir/out/WhirVerifier.sol/WhirVerifier.json"));
        GkrWhirRegistry(REGISTRY).initialize_verifiers(GKR_TWO_TX, WHIR_TWO_TX);
        vm.recordLogs();
        (bool gkrOk,) = GKR_TWO_TX.call(gkrCalldata);
        require(gkrOk, "two-tx GKR must verify");
        Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "expected one GKR mark");
        (bytes32 pi2, bytes32 sc2) = abi.decode(logs[0].data, (bytes32, bytes32));
        (bool whirOk,) = WHIR_TWO_TX.call(whirCalldata);
        require(whirOk, "two-tx WHIR must verify");
        bytes32 c2 = logs[0].topics[1];
        require(
            GkrWhirRegistry(REGISTRY).verificationMask(c2) == GkrWhirRegistry.VerificationMask.Both,
            "two-tx pair was not accepted"
        );
        (bytes32 c1, bytes32 pi1, bytes32 sc1) = _accept(verifier, single);
        require(c1 == c2 && pi1 == pi2 && sc1 == sc2, "single-tx result differs from the two-tx registry");
    }

    function test_rejects_wrong_final_pc() public {
        _accept(verifier, single);
        L1VerifierSingleTx wrongPc = new L1VerifierSingleTx(GKR_WRONG_PC, WHIR, gkrCalldata.length);
        require(_rejects(wrongPc, single), "wrong expected final PC accepted");
    }

    function test_rejects_flipped_final_pc_transcript() public {
        _accept(verifier, single);
        bytes memory bad = bytes.concat(single);
        _flipField(bad, ".gkr.final_pc", 4, "u32_le");
        require(_rejects(verifier, bad), "changed final PC accepted");
    }

    function test_rejects_wrong_pow_nonce() public {
        _accept(verifier, single);
        bytes memory bad = bytes.concat(single);
        _flipField(bad, ".gkr.external_pow_nonce", 8, "u64_be");
        require(_rejects(verifier, bad), "changed external PoW nonce accepted");
    }

    function test_rejects_tampered_gkr_bytes() public {
        _accept(verifier, single);
        uint256[3] memory at = [plen + 64, gkrCalldata.length / 2, gkrCalldata.length - 1];
        for (uint256 i; i < at.length; ++i) {
            bytes memory bad = bytes.concat(single);
            bad[at[i]] ^= bytes1(uint8(1));
            require(_rejects(verifier, bad), "tampered GKR byte accepted");
        }
    }

    /// WHIR stream bytes: first sumcheck coefficient, middle, and the last byte (final query path).
    function test_rejects_tampered_whir_bytes() public {
        _accept(verifier, single);
        uint256 g = gkrCalldata.length;
        uint256[3] memory at = [g + 15, g + (single.length - g) / 2, single.length - 1];
        for (uint256 i; i < at.length; ++i) {
            bytes memory bad = bytes.concat(single);
            bad[at[i]] ^= bytes1(uint8(1));
            require(_rejects(verifier, bad), "tampered WHIR byte accepted");
        }
    }

    function test_rejects_truncated_or_extended() public {
        _accept(verifier, single);
        require(_rejects(verifier, _slice(single, 0, single.length - 1)), "truncated proof accepted");
        require(_rejects(verifier, bytes.concat(single, hex"00")), "extended proof accepted");
        require(_rejects(verifier, _slice(single, 0, gkrCalldata.length)), "GKR half alone accepted");
    }

    /// This proof's GKR half + the WHIR stream of another valid same-shape 2^21 proof.
    function test_rejects_mismatched_halves() public {
        _accept(verifier, single);
        bytes memory alt = _calldata("./testdata/alt_whir_calldata.hex");
        require(keccak256(alt) != keccak256(whirCalldata), "alt proof is this proof");
        // Control: the alt WHIR proof is valid on its own (two-tx form, its own preimage).
        (bool altOk, bytes memory altRet) = WHIR.call(alt);
        require(altOk, "alt WHIR proof must verify on its own");
        (,,, bytes32 altCommitment) = abi.decode(altRet, (uint256, uint256, uint256, bytes32));
        require(altCommitment != keccak256(_slice(whirCalldata, 0, plen)), "alt committed state equals this one");
        bytes memory mixed = bytes.concat(gkrCalldata, _slice(alt, plen, alt.length));
        require(_rejects(verifier, mixed), "mismatched halves accepted");
    }

    /// No ABI surface: every input that is not a valid proof reverts, including short inputs and
    /// the selectors of the (former) immutable getters.
    function test_rejects_selector_only_inputs() public {
        _accept(verifier, single);
        bytes4[4] memory sels = [bytes4(0xb969ce40), bytes4(0xb9a88d16), bytes4(0x08b39c85), bytes4(0)];
        for (uint256 i; i < sels.length; ++i) {
            require(_rejects(verifier, abi.encodePacked(sels[i])), "selector-only input accepted");
        }
        require(_rejects(verifier, ""), "empty input accepted");
    }

    /// The commitment comparison is load-bearing: a WHIR result with another commitment is rejected.
    function test_rejects_commitment_mismatch() public {
        _accept(verifier, single);
        L1VerifierSingleTx bad = new L1VerifierSingleTx(GKR, address(new WrongCommitmentWhir()), gkrCalldata.length);
        require(_rejects(bad, single), "commitment mismatch accepted");
    }
}
