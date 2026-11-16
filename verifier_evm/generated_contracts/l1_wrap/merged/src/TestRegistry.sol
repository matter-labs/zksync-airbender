// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.38;

import {IVerificationRegistry} from "./GkrWhirVerifier.sol";

/// Minimal `IVerificationRegistry` for tests and local deployments: records every statement a
/// verifier reports (`markVerified`), keyed by (msg.sender, publicInput, auxInput), and keeps
/// the last mark + its reporter for inspection. Anyone may call it and any chain is accepted
/// — a production registry accepts only approved verifier addresses (`msg.sender`), each
/// pinned to one setup embedded in its runtime code, and compares `auxInput` with the expected
/// recursion chain hash.
contract TestRegistry is IVerificationRegistry {
    struct Mark {
        bytes32 publicInput;
        bytes32 auxInput;
    }

    event MarkedVerified(address indexed verifier, bytes32 publicInput, bytes32 auxInput);

    /// Number of marks recorded so far.
    uint256 public count;
    /// The most recent mark and who reported it.
    Mark public last;
    address public lastVerifier;
    /// keccak256(abi.encode(msg.sender, publicInput, auxInput)) => recorded
    mapping(bytes32 => bool) public isVerified;

    function markVerified(bytes32 publicInput, bytes32 auxInput) external override {
        count += 1;
        last = Mark(publicInput, auxInput);
        lastVerifier = msg.sender;
        isVerified[keccak256(abi.encode(msg.sender, publicInput, auxInput))] = true;
        emit MarkedVerified(msg.sender, publicInput, auxInput);
    }
}
