// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

/// F1 ↔ v0 oracle on the merged verifiers: the instrumented renders (`../instrumented/{v0,f1}`)
/// log every keccak256 result except Merkle leaf and node hashes (transcript absorbs and draws,
/// PoW digests, query draws, the setup commitment) and return
/// `[count][hashes][publicInput, auxInput, setupCommitment]` instead of calling the registry. On
/// the same proof the F1 render must return exactly the v0 render's log and statement.
///   forge test -vv --match-contract F1OracleTest --disable-code-size-limit

import {TestRegistry} from "../src/TestRegistry.sol";
import {MergedBase} from "./MergedBase.sol";

contract F1OracleTest is MergedBase {
    function test_log_and_statement_equal_v0() external {
        _placeFrontier();
        address registry = address(new TestRegistry());
        address v0 = _deploy("../instrumented/v0/out/GkrWhirVerifier.sol/GkrWhirVerifier.json", registry);
        address f1 = _deploy("../instrumented/f1/out/GkrWhirVerifier.sol/GkrWhirVerifier.json", registry);
        bytes memory r0 = _accepts(v0, _hex(string.concat(DATA, "merged_calldata.hex")));
        bytes memory r1 = _accepts(f1, _hex(string.concat(DATA, "single_tx_f1.hex")));
        uint256 count = uint256(_slice32(r0, 0));
        require(count > 0 && r0.length == 32 * (count + 1) + 96, "malformed instrumented return");
        require(keccak256(r0) == keccak256(r1), "F1 keccak log or statement differs from v0");
        bytes memory expected = _hex(string.concat(DATA, "verified_mark.hex"));
        require(keccak256(_slice(r0, r0.length - 96, r0.length)) == keccak256(expected), "statement != Rust mark");
    }
}
