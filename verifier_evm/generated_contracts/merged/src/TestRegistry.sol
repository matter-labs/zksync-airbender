// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.36;

import {IVerificationRegistry} from "./GkrWhirVerifier.sol";

/// Minimal `IVerificationRegistry` for tests and local deployments: records every statement a
/// verifier reports (`markVerified`), keyed by the full (publicInput, auxInput, setupCommitment)
/// tuple, and keeps the last mark + its reporter for inspection. Anyone may call it — a
/// production registry would restrict `msg.sender` to the trusted verifier(s).
contract TestRegistry is IVerificationRegistry {
    struct Mark {
        bytes32 publicInput;
        bytes32 auxInput;
        bytes32 setupCommitment;
    }

    event MarkedVerified(
        address indexed verifier, bytes32 publicInput, bytes32 auxInput, bytes32 setupCommitment
    );

    /// Number of marks recorded so far.
    uint256 public count;
    /// The most recent mark and who reported it.
    Mark public last;
    address public lastVerifier;
    /// keccak256(abi.encode(publicInput, auxInput, setupCommitment)) => recorded
    mapping(bytes32 => bool) public isVerified;

    function markVerified(bytes32 publicInput, bytes32 auxInput, bytes32 setupCommitment) external override {
        count += 1;
        last = Mark(publicInput, auxInput, setupCommitment);
        lastVerifier = msg.sender;
        isVerified[keccak256(abi.encode(publicInput, auxInput, setupCommitment))] = true;
        emit MarkedVerified(msg.sender, publicInput, auxInput, setupCommitment);
    }
}
