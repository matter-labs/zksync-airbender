// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.36;

import {InitializationWindows} from "../src/InitializationWindows.sol";
import {GkrWhirVerifier as GeneratedGKR} from "../src/GkrVerifier.sol";
import {GkrWhirVerifierFixture as CommittedGKR} from "../src/GkrWhirVerifierFixture.sol";

interface WindowTestVm {
    function readFileBinary(string calldata path) external view returns (bytes memory);
}

contract WindowTestRegistry {
    function markVerified(bytes32, bytes32, bytes32) external {}
}

contract InitializationWindowsReplayTest {
    WindowTestVm constant vm = WindowTestVm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    function testExistingValidMergedProofStillVerifies() public {
        bytes memory proof = vm.readFileBinary("fixtures/gkr-calldata.bin");
        (bool generatedAccepted,) = address(new GeneratedGKR(address(new WindowTestRegistry()))).call(proof);
        require(generatedAccepted, "regenerated verifier rejected valid proof");
        (bool committedAccepted,) = address(new CommittedGKR(address(new WindowTestRegistry()))).call(proof);
        require(committedAccepted, "committed verifier rejected valid proof");
    }
}

contract InitializationWindowsTest {
    InitializationWindows private validator;

    function setUp() public {
        validator = new InitializationWindows();
    }

    // The protocol preimage has 32 twelve-byte register records, then twelve
    // bytes for final PC/clock, followed by two little-endian u32 indices.
    function payload(uint32 first, uint32 second) private pure returns (bytes memory data) {
        data = new bytes(404);
        for (uint256 i; i < 4; ++i) {
            data[396 + i] = bytes1(uint8(first >> (8 * i)));
            data[400 + i] = bytes1(uint8(second >> (8 * i)));
        }
    }

    function check(bytes memory data, bool expected) private {
        (bool accepted,) = address(validator).call(data);
        require(accepted == expected, "unexpected window validation");
    }

    function testValidSparseAndReversedWindows() public {
        check(payload(0, 1), true);
        check(payload(0, 255), true);
        check(payload(64, 255), true);
        check(payload(254, 255), true);
        check(payload(255, 254), true);
    }

    function testDuplicateWindows() public {
        check(payload(0, 0), false);
        check(payload(17, 17), false);
        check(payload(254, 254), false);
        check(payload(255, 255), false);
    }

    function testFullU32RangeAndLittleEndianDecoding() public {
        check(payload(256, 1), false);
        check(payload(1, 256), false);
        check(payload(0x01000000, 1), false);
        check(payload(1, 0x01000000), false);
        check(payload(type(uint32).max, 1), false);
        check(payload(1, type(uint32).max), false);
    }

    function testTruncatedWindowBlock() public {
        check(new bytes(0), false);
        check(new bytes(395), false);
        bytes memory data = payload(0, 1);
        for (uint256 length = 396; length < 404; ++length) {
            bytes memory truncated = new bytes(length);
            for (uint256 i; i < length; ++i) truncated[i] = data[i];
            check(truncated, false);
        }
    }

    function testAdjacentStatementBytesAreNotWindowBits() public {
        bytes memory data = bytes.concat(payload(254, 255), hex"ffffffffffffffff");
        for (uint256 i; i < 396; ++i) data[i] = 0xff;
        check(data, true);
    }

    function testFuzzInRange(uint8 first, uint8 second) public {
        check(payload(first, second), first != second);
    }

    function testFuzzFullU32(uint32 first, uint32 second) public {
        check(payload(first, second), first < 256 && second < 256 && first != second);
    }
}
