//! Single-transaction variants of the generated two-tx verifiers, for the
//! `L1VerifierSingleTx` proxy: tx calldata = GKR proof ‖ WHIR proof stream, the WHIR
//! committed-state preimage comes from the GKR verifier's return data.
//!
//! - GKR: the `mark_gkr_verified` registry call is replaced by
//!   `return([preimage][commitment][public_input][setup_commitment])`.
//! - WHIR: the `mark_whir_verified` registry call is removed and the final return also
//!   carries the recomputed commitment (already at `COMMIT_PTR` = 96).
//!
//! Every other line of the two-tx source is unchanged.

const GKR_MARK: &str = "            let commitment := keccak256(base, plen)
            // public_input = registers x10..x17 (a0..a7); setup_commitment = x18..x25 (s2..s9).
            // Each register's u32 value is stored LE at preimage byte reg*12; concatenate the
            // 8 4-byte LE values into a 32-byte word (reuse `base` scratch, now that the
            // commitment is hashed).
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                calldatacopy(add(base, mul(i, 4)), mul(add(10, i), 12), 4)
            }
            let pubval := mload(base)
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                calldatacopy(add(base, mul(i, 4)), mul(add(18, i), 12), 4)
            }
            let setupval := mload(base)
            // mark_gkr_verified(commitment, public_input, setup_commitment)
            mstore(0, shl(224, MARK_GKR_SELECTOR))
            mstore(4, commitment)
            mstore(36, pubval)
            mstore(68, setupval)
            pop(call(gas(), __TEMPLATE_REGISTRY_ADDRESS, 0, 0, 100, 0, 0))
";

const GKR_RETURN: &str = "            let commitment := keccak256(base, plen)
            // public_input = registers x10..x17 (a0..a7); setup_commitment = x18..x25 (s2..s9).
            // Each register's u32 value is stored LE at preimage byte reg*12; concatenate the
            // 8 4-byte LE values into a 32-byte word, written after the preimage (kept intact).
            let pd := add(base, plen)
            mstore(pd, commitment)
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                calldatacopy(add(add(pd, 32), mul(i, 4)), mul(add(10, i), 12), 4)
            }
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                calldatacopy(add(add(pd, 64), mul(i, 4)), mul(add(18, i), 12), 4)
            }
            // single-tx: return [preimage][commitment][public_input][setup_commitment]
            return(base, add(plen, 96))
";

const WHIR_MARK: &str =
    "        // Every check passed (any failure would have reverted). Notify the registry with
        // the recomputed committed state — GKR marks the same bytes32 from its own tx.
        {
            mstore(0, shl(224, MARK_WHIR_SELECTOR))
            mstore(4, mload(COMMIT_PTR))
            pop(call(gas(), __TEMPLATE_REGISTRY_ADDRESS, 0, 0, 36, 0, 0))
        }
";

const WHIR_NO_MARK: &str =
    "        // Every check passed (any failure would have reverted). single-tx: the recomputed
        // committed state stays at COMMIT_PTR (96) and is returned below.
";

const WHIR_RETURN: &str = "        mstore(64, mload(REG_CD))
        return(0, 96)
";

const WHIR_RETURN_COMMITMENT: &str = "        mstore(64, mload(REG_CD))
        return(0, 128) // [claim][verify_gas][cd][commitment]
";

fn replace_once(src: &str, old: &str, new: &str, what: &str) -> String {
    assert_eq!(
        src.matches(old).count(),
        1,
        "single-tx {what}: anchor must occur exactly once"
    );
    src.replacen(old, new, 1)
}

/// The single-tx variant of a generated two-tx GKR verifier source.
pub fn single_tx_gkr(gkr_sol: &str) -> String {
    replace_once(gkr_sol, GKR_MARK, GKR_RETURN, "GKR registry mark")
}

/// The single-tx variant of a generated two-tx WHIR verifier source.
pub fn single_tx_whir(whir_sol: &str) -> String {
    let whir = replace_once(whir_sol, WHIR_MARK, WHIR_NO_MARK, "WHIR registry mark");
    replace_once(&whir, WHIR_RETURN, WHIR_RETURN_COMMITMENT, "WHIR return")
}
