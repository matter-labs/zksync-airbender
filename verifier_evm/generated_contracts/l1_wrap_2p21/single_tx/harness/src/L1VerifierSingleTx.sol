// SPDX-License-Identifier: MIT
pragma solidity =0.8.36;

/// Single-transaction proxy over the generated single-tx GKR and WHIR verifiers (measurement
/// harness, no storage). tx calldata = GKR proof ‖ WHIR proof stream; the WHIR committed-state
/// preimage [seed][batching][opening][z_initial][memory_cap][setup_cap] is NOT in calldata.
/// 1. CALL GKR(GKR proof) -> [preimage][commitment][public_input][setup_commitment].
/// 2. CALL WHIR(preimage ‖ WHIR stream), built in memory -> [claim][verify_gas][cd][commitment].
/// Accept iff both calls succeed and the two commitments are equal (the two-tx registry's
/// acceptance condition: both verifiers marked the same committed state).
/// Returns [commitment][public_input][setup_commitment].
contract L1VerifierSingleTx {
    address private immutable gkrVerifier;
    address private immutable whirVerifier;
    uint256 private immutable gkrProofLength;

    constructor(address gkrVerifier_, address whirVerifier_, uint256 gkrProofLength_) {
        gkrVerifier = gkrVerifier_;
        whirVerifier = whirVerifier_;
        gkrProofLength = gkrProofLength_;
    }

    fallback() external {
        address gkr = gkrVerifier;
        address whir = whirVerifier;
        uint256 glen = gkrProofLength;
        assembly {
            if lt(calldatasize(), glen) { revert(0, 0) }
            let buf := 0x80
            calldatacopy(buf, 0, glen)
            if iszero(call(gas(), gkr, 0, buf, glen, 0, 0)) { revert(0, 0) }
            if lt(returndatasize(), 96) { revert(0, 0) }
            let plen := sub(returndatasize(), 96)
            let wlen := sub(calldatasize(), glen)
            let res := add(buf, add(plen, wlen))
            returndatacopy(res, plen, 96)
            returndatacopy(buf, 0, plen)
            calldatacopy(add(buf, plen), glen, wlen)
            if iszero(call(gas(), whir, 0, buf, add(plen, wlen), 0, 0)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 128)) { revert(0, 0) }
            returndatacopy(0, 96, 32)
            if iszero(eq(mload(0), mload(res))) { revert(0, 0) }
            return(res, 96)
        }
    }
}
