// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.24;

contract GKRVerifier {
    // ── Generic (used throughout) ───────────────────────────────────────────
    uint256 constant P      = 0xffffffffffffffffffffffffffffff61; // 2^128 - 159
    uint256 constant MASK   = 0xffffffffffffffffffffffffffffffff; // high 128 bits
    uint256 constant ROUNDS = 200;
    // Fiat-Shamir transcript region: seed at [SEED_PTR, SEED_PTR+32), absorb
    // scratch above it. Every transcript helper uses this, never a hardcoded
    // 0/32/64, so the layout can be relocated in one place.
    uint256 constant SEED_PTR = 5000; // TODO: move back down

    // ── Transcript init (absorb caps, derive memory/logup challenges) ─────────
    uint256 constant MERKLE_TREE_CAPS_BYTES = 512; // 16 caps * 32-byte hash
    uint256 constant MEMORY_CHALLS_PTR      = 768; // 7 elems: 6 tuple-compression + 1 additive
    uint256 constant LOGUP_CHALLS_PTR       = 992; // 2 elems: 1 tuple-compression + 1 additive

    // ── GKR init (fold the 8 init polys into the first sumcheck claim) ────────
    uint256 constant GKR_INIT_BYTES          = 2048; // 8 polys * 16 elems * 16 bytes
    uint256 constant GKR_INIT_POLY_BYTES     = 256;  // 16 elems * 16 bytes (literal; Yul rejects const exprs)
    uint256 constant POINT_PTR               = 0;    // z1..z4 / point batch at [0, 768), below the transcript region
    uint256 constant GKR_INIT_EQ_PTR0        = 2496; // fold-accumulator scratch slot (legacy eq-table name)
    uint256 constant CLAIM_PTR               = 3000;
    uint256 constant GKR_STREAMREV_CLAIM_PTR = 4512;
    uint256 constant GKR_INIT_GAS_PTR        = 4256; // stash gas() across init so Yul/solx spills can't clobber it
    uint256 constant GKR_INIT_PTR            = 2048; // testing: hardcoded init pointer

    // ── GKR compression ───────────────────────────────────────────────────────
    uint256 constant GKR_COMPRESSION_POINTCHECK_POLY_BYTES = 64;  // 4 * 16
    uint256 constant GKR_COMPRESSION_POINTCHECK_BYTES      = 512; // 8 * 64
    uint256 constant GKR_COMPRESS_GAS_PTR    = 4288;

    // ── GKR circuit ───────────────────────────────────────────────────────────
    uint256 constant GKR_CIRCUIT_CACHE_PTR    = 5032; // = SEED_PTR - 32*10; shares the transcript absorb region
    uint256 constant GKR_CIRCUIT_LAYER_ROUNDS = 24;

    fallback() external {
        // uint256 variant = VARIANT;
        assembly {
        // assembly ("memory-safe") {
        // Proof/transcript bytes preserve logical stream order. Rust must append
        // fixed-width BE integer bytes: u32::to_be_bytes(), u64::to_be_bytes(),
        // u128::to_be_bytes(). 32-byte hashes/caps/roots are absorbed as raw bytes.
        // For u128 pairs calldata is [x0:16][x1:16], so x0 is shr(128, word)
        // and x1 is and(word, MASK). Smaller lanes follow the same BE packing rule
        // with larger shifts. Hash challenges use the earlier 16 hash bytes
        // first: shr(128, seed), then and(seed, MASK).

        function transcript_4to1_dual(w0, w1) -> r {
            // put to memory 4 coeffs from w0, w1, after SEED (prev hash, FS chain)
            mstore(add(SEED_PTR, 64), w1)
            mstore(add(SEED_PTR, 32), w0)
            let seed := keccak256(SEED_PTR, 96) // hash SEED + 4 coeffs to stack word
            mstore(SEED_PTR, seed) // immediately dump SEED
            r := shr(128, seed)
        }

        // alpha is the batching challenge needed right after checking outputs
        function transcript128to5_once(ptr) -> z1, z2, z3, z4, alpha {
            calldatacopy(add(SEED_PTR, 32), ptr, GKR_INIT_BYTES)

            let seed := keccak256(SEED_PTR, add(32, GKR_INIT_BYTES))
            mstore(SEED_PTR, seed)
            z1 := shr(128, seed)
            z2 := and(seed, MASK)

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            z3 := shr(128, seed)
            z4 := and(seed, MASK)

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            alpha := shr(128, seed)
        }



        // alpha is the batching challenge needed right folding point claims
        function transcript32to3(ptr) -> z1, z2, alpha {
            calldatacopy(add(SEED_PTR, 32), ptr, GKR_COMPRESSION_POINTCHECK_BYTES)

            let seed := keccak256(SEED_PTR, add(32, GKR_COMPRESSION_POINTCHECK_BYTES))
            mstore(SEED_PTR, seed)
            z1 := shr(128, seed)
            z2 := and(seed, MASK)

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            alpha := shr(128, seed)
        }

        function transcript_init(ptr) -> next_ptr {
            // TODO: we are missing FINAL regs val/ts + FINAL pc/ts
            
            // FIRST: absorb mem caps -> get 7 mem challs
            calldatacopy(add(SEED_PTR, 32), ptr, MERKLE_TREE_CAPS_BYTES)
            let seed := keccak256(SEED_PTR, add(32, MERKLE_TREE_CAPS_BYTES))
            mstore(SEED_PTR, seed)
            mstore(MEMORY_CHALLS_PTR, shr(128, seed))
            mstore(add(MEMORY_CHALLS_PTR, 32), and(seed, MASK))

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            mstore(add(MEMORY_CHALLS_PTR, 64), shr(128, seed))
            mstore(add(MEMORY_CHALLS_PTR, 96), and(seed, MASK))

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            mstore(add(MEMORY_CHALLS_PTR, 128), shr(128, seed))
            mstore(add(MEMORY_CHALLS_PTR, 160), and(seed, MASK))

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            mstore(add(MEMORY_CHALLS_PTR, 192), shr(128, seed))

            // SECOND: absorb wit+setup caps -> get 2 logup challs
            ptr := add(ptr, MERKLE_TREE_CAPS_BYTES)
            calldatacopy(add(SEED_PTR, 32), ptr, mul(2, MERKLE_TREE_CAPS_BYTES))
            seed := keccak256(SEED_PTR, add(32, mul(2, MERKLE_TREE_CAPS_BYTES)))
            mstore(SEED_PTR, seed)
            mstore(LOGUP_CHALLS_PTR, shr(128, seed))
            mstore(add(LOGUP_CHALLS_PTR, 32), and(seed, MASK))

            next_ptr := add(ptr, mul(2, MERKLE_TREE_CAPS_BYTES))
        }

        function acceval_inlinefold_streamrevlooploop_evenodd(ptr, z1, z2, z3, z4, alpha) -> claim {
            // TODO: inject final values (regs, pc)
            // NB: some stack values are explicitly spilled (fold0 and claim updates):
            //     - when written to, it is after stored
            //     - when read, it is first loaded
            // Same current READ+WRITE work as the open-coded even/odd path, but
            // factored into four quarter chunks under a loop.

            mstore(CLAIM_PTR, claim)
            for { let poly := 6 } gt(poly, 0) { poly := sub(poly, 2) } {
                let num_acc
                let den_acc := 1
                let numfold0, numfold1, numfold2, numfold3
                let denfold0, denfold1, denfold2, denfold3
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let numbase := add(add(ptr, mul(poly, GKR_INIT_POLY_BYTES)), mul(i, 64))
                    let denbase := add(add(ptr, mul(add(poly, 1), GKR_INIT_POLY_BYTES)), mul(i, 64))

                    // fold i+0/1
                    let numword0 := calldataload(numbase)
                    let num0 := shr(128, numword0)
                    let num1 := and(MASK, numword0)
                    let denword0 := calldataload(denbase)
                    let den0 := shr(128, denword0)
                    let den1 := and(MASK, denword0)
                    num_acc := add(mulmod(num_acc, den0, P), mulmod(den_acc, num0, P))
                    den_acc := mulmod(den_acc, den0, P)
                    num_acc := add(mulmod(num_acc, den1, P), mulmod(den_acc, num1, P))
                    den_acc := mulmod(den_acc, den1, P)
                    let numfolda := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                    let denfolda := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))

                    // fold i+2/3
                    let numword1 := calldataload(add(numbase, 32))
                    let num2 := shr(128, numword1)
                    let num3 := and(MASK, numword1)
                    let denword1 := calldataload(add(denbase, 32))
                    let den2 := shr(128, denword1)
                    let den3 := and(MASK, denword1)
                    num_acc := add(mulmod(num_acc, den2, P), mulmod(den_acc, num2, P))
                    den_acc := mulmod(den_acc, den2, P)
                    num_acc := add(mulmod(num_acc, den3, P), mulmod(den_acc, num3, P))
                    den_acc := mulmod(den_acc, den3, P)
                    let numfoldb := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                    let denfoldb := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))

                    // fold i+0/1/2/3
                    let numfoldc := add(numfolda, mulmod(z3, sub(add(numfoldb, mul(3, P)), numfolda), P))
                    let denfoldc := add(denfolda, mulmod(z3, sub(add(denfoldb, mul(3, P)), denfolda), P))
                    switch i
                    case 0 {
                        numfold0 := numfoldc
                        mstore(GKR_INIT_EQ_PTR0, numfold0)
                        denfold0 := denfoldc
                    }
                    case 1 {
                        numfold1 := numfoldc
                        denfold1 := denfoldc
                    }
                    case 2 {
                        numfold2 := numfoldc
                        denfold2 := denfoldc
                    }
                    default {
                        numfold3 := numfoldc
                        denfold3 := denfoldc
                    }
                }
                // check
                if mod(num_acc, P) { revert(0, 0) }
                if iszero(den_acc) { revert(0, 0) }
                // fold 0/1/2/3/4/5/6/7
                numfold0 := mload(GKR_INIT_EQ_PTR0)
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                let num_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                let den_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
                // batch
                claim := mload(CLAIM_PTR)
                claim := add(mulmod(claim, alpha, P), den_claim)
                claim := add(mulmod(claim, alpha, P), num_claim)
                mstore(CLAIM_PTR, claim)
            }

            let write_acc
            for { let poly := 1 } lt(poly, 2) { poly := sub(poly, 1) } {
                let prod_acc := 1
                let fold0, fold1, fold2, fold3
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let base := add(add(ptr, mul(poly, GKR_INIT_POLY_BYTES)), mul(i, 64))
                    // fold i+0/1
                    let word0 := calldataload(base)
                    let prod0 := shr(128, word0)
                    let prod1 := and(MASK, word0)
                    prod_acc := mulmod(prod_acc, prod0, P)
                    prod_acc := mulmod(prod_acc, prod1, P)
                    let folda := add(prod0, mulmod(z4, sub(add(prod1, mul(2, P)), prod0), P))
                    // fold i+2/3
                    let word1 := calldataload(add(base, 32))
                    let prod2 := shr(128, word1)
                    let prod3 := and(MASK, word1)
                    prod_acc := mulmod(prod_acc, prod2, P)
                    prod_acc := mulmod(prod_acc, prod3, P)
                    let foldb := add(prod2, mulmod(z4, sub(add(prod3, mul(2, P)), prod2), P))
                    // fold i+0/1/2/3
                    let foldc := add(folda, mulmod(z3, sub(add(foldb, mul(3, P)), folda), P))
                    switch i
                    case 0 {
                        fold0 := foldc
                        mstore(GKR_INIT_EQ_PTR0, fold0)
                    }
                    case 1 { fold1 := foldc }
                    case 2 { fold2 := foldc }
                    default { fold3 := foldc }
                }
                // check
                if iszero(poly) {
                    let read_acc := prod_acc
                    if iszero(eq(read_acc, write_acc)) { revert(0, 0) }
                }
                write_acc := prod_acc
                // fold 0/1/2/3/4/5/6/7
                fold0 := mload(GKR_INIT_EQ_PTR0)
                fold0 := add(fold0, mulmod(z2, sub(add(fold1, mul(4, P)), fold0), P))
                // fold 8/9/10/11/12/13/14/15
                fold1 := add(fold2, mulmod(z2, sub(add(fold3, mul(4, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                let prod_claim := add(fold0, mulmod(z1, sub(add(fold1, mul(5, P)), fold0), P))
                // batch
                claim := mload(CLAIM_PTR)
                claim := add(mulmod(claim, alpha, P), prod_claim)
                mstore(CLAIM_PTR, claim)
            }
            claim := mload(CLAIM_PTR)
        }

        function acceval_inlinefold_streamrevlooploop_evenodd_newunchecked(ptr, z1, z2, z3, z4, alpha) -> claim {
            // TODO: inject final values (regs, pc)
            // TODO: this was made by AI, needs to be reviewed
            // NB: some stack values are explicitly spilled (fold0 and claim updates):
            //     - when written to, it is after stored
            //     - when read, it is first loaded
            // Same current READ+WRITE work as the open-coded even/odd path, but
            // factored into four quarter chunks under a loop.

            mstore(CLAIM_PTR, claim)
            for { let poly := 6 } gt(poly, 0) { poly := sub(poly, 2) } {
                {
                    let num_acc
                    let den_acc := 1
                    for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                        let numbase := add(add(ptr, mul(poly, GKR_INIT_POLY_BYTES)), mul(i, 64))
                        let denbase := add(add(ptr, mul(add(poly, 1), GKR_INIT_POLY_BYTES)), mul(i, 64))
                        let numword0 := calldataload(numbase)
                        let num0 := shr(128, numword0)
                        let num1 := and(MASK, numword0)
                        let denword0 := calldataload(denbase)
                        let den0 := shr(128, denword0)
                        let den1 := and(MASK, denword0)
                        num_acc := add(mulmod(num_acc, den0, P), mulmod(den_acc, num0, P))
                        den_acc := mulmod(den_acc, den0, P)
                        num_acc := add(mulmod(num_acc, den1, P), mulmod(den_acc, num1, P))
                        den_acc := mulmod(den_acc, den1, P)
                        let numword1 := calldataload(add(numbase, 32))
                        let num2 := shr(128, numword1)
                        let num3 := and(MASK, numword1)
                        let denword1 := calldataload(add(denbase, 32))
                        let den2 := shr(128, denword1)
                        let den3 := and(MASK, denword1)
                        num_acc := add(mulmod(num_acc, den2, P), mulmod(den_acc, num2, P))
                        den_acc := mulmod(den_acc, den2, P)
                        num_acc := add(mulmod(num_acc, den3, P), mulmod(den_acc, num3, P))
                        den_acc := mulmod(den_acc, den3, P)
                    }
                    if mod(num_acc, P) { revert(0, 0) }
                    if iszero(den_acc) { revert(0, 0) }
                }
                {
                    let numfold0, numfold1, numfold2, numfold3
                    let denfold0, denfold1, denfold2, denfold3
                    for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                        let numbase := add(add(ptr, mul(poly, GKR_INIT_POLY_BYTES)), mul(i, 64))
                        let denbase := add(add(ptr, mul(add(poly, 1), GKR_INIT_POLY_BYTES)), mul(i, 64))
                        let numword0 := calldataload(numbase)
                        let num0 := shr(128, numword0)
                        let num1 := and(MASK, numword0)
                        let denword0 := calldataload(denbase)
                        let den0 := shr(128, denword0)
                        let den1 := and(MASK, denword0)
                        let numfolda := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                        let denfolda := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))
                        let numword1 := calldataload(add(numbase, 32))
                        let num2 := shr(128, numword1)
                        let num3 := and(MASK, numword1)
                        let denword1 := calldataload(add(denbase, 32))
                        let den2 := shr(128, denword1)
                        let den3 := and(MASK, denword1)
                        let numfoldb := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                        let denfoldb := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))
                        let numfoldc := add(numfolda, mulmod(z3, sub(add(numfoldb, mul(3, P)), numfolda), P))
                        let denfoldc := add(denfolda, mulmod(z3, sub(add(denfoldb, mul(3, P)), denfolda), P))
                        switch i
                        case 0 { numfold0 := numfoldc mstore(GKR_INIT_EQ_PTR0, numfold0) denfold0 := denfoldc }
                        case 1 { numfold1 := numfoldc denfold1 := denfoldc }
                        case 2 { numfold2 := numfoldc denfold2 := denfoldc }
                        default { numfold3 := numfoldc denfold3 := denfoldc }
                    }
                    numfold0 := mload(GKR_INIT_EQ_PTR0)
                    numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                    denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))
                    numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                    denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                    let num_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                    let den_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
                    let term_ptr := add(GKR_STREAMREV_CLAIM_PTR, mul(sub(6, poly), 32))
                    mstore(term_ptr, den_claim)
                    mstore(add(term_ptr, 32), num_claim)
                }
            }

            let write_acc
            for { let poly := 1 } lt(poly, 2) { poly := sub(poly, 1) } {
                {
                    let prod_acc := 1
                    for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                        let base := add(add(ptr, mul(poly, GKR_INIT_POLY_BYTES)), mul(i, 64))
                        let word0 := calldataload(base)
                        prod_acc := mulmod(prod_acc, shr(128, word0), P)
                        prod_acc := mulmod(prod_acc, and(MASK, word0), P)
                        let word1 := calldataload(add(base, 32))
                        prod_acc := mulmod(prod_acc, shr(128, word1), P)
                        prod_acc := mulmod(prod_acc, and(MASK, word1), P)
                    }
                    if iszero(poly) {
                        let read_acc := prod_acc
                        if iszero(eq(read_acc, write_acc)) { revert(0, 0) }
                    }
                    write_acc := prod_acc
                }
                {
                    let fold0, fold1, fold2, fold3
                    for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                        let base := add(add(ptr, mul(poly, GKR_INIT_POLY_BYTES)), mul(i, 64))
                        let word0 := calldataload(base)
                        let prod0 := shr(128, word0)
                        let prod1 := and(MASK, word0)
                        let folda := add(prod0, mulmod(z4, sub(add(prod1, mul(2, P)), prod0), P))
                        let word1 := calldataload(add(base, 32))
                        let prod2 := shr(128, word1)
                        let prod3 := and(MASK, word1)
                        let foldb := add(prod2, mulmod(z4, sub(add(prod3, mul(2, P)), prod2), P))
                        let foldc := add(folda, mulmod(z3, sub(add(foldb, mul(3, P)), folda), P))
                        switch i
                        case 0 { fold0 := foldc mstore(GKR_INIT_EQ_PTR0, fold0) }
                        case 1 { fold1 := foldc }
                        case 2 { fold2 := foldc }
                        default { fold3 := foldc }
                    }
                    fold0 := mload(GKR_INIT_EQ_PTR0)
                    fold0 := add(fold0, mulmod(z2, sub(add(fold1, mul(4, P)), fold0), P))
                    fold1 := add(fold2, mulmod(z2, sub(add(fold3, mul(4, P)), fold2), P))
                    let prod_claim := add(fold0, mulmod(z1, sub(add(fold1, mul(5, P)), fold0), P))
                    mstore(add(GKR_STREAMREV_CLAIM_PTR, sub(224, mul(poly, 32))), prod_claim)
                }
            }
            claim := 0
            for { let off := 0 } lt(off, 256) { off := add(off, 32) } {
                claim := add(mulmod(claim, alpha, P), mload(add(GKR_STREAMREV_CLAIM_PTR, off)))
            }
        }

        // Strategy 2: absorb the init block and draw z1..z4 and alpha, but do not
        // store full eq[16]. Instead, generate eq factors inline while streaming
        // over calldata so folding and accumulator updates happen in one pass.
        function gkr_init_inlinefold(ptr) -> next_ptr, claim, alpha {
            let z1, z2, z3, z4
            z1, z2, z3, z4, alpha := transcript128to5_once(ptr)
            mstore(POINT_PTR, z1)
            mstore(add(POINT_PTR, 32), z2)
            mstore(add(POINT_PTR, 64), z3)
            mstore(add(POINT_PTR, 96), z4)

            // claim := acceval_inlinefold_streamrevlooploop_evenodd(ptr, z1, z2, z3, z4, alpha)
            claim := acceval_inlinefold_streamrevlooploop_evenodd_newunchecked(ptr, z1, z2, z3, z4, alpha)

            next_ptr := add(ptr, GKR_INIT_BYTES)
        }

        function sumcheck_round_dual(ptr, claim) -> next_ptr, next_claim {
            // TODO: the two mods can be batched into one mod + maybe a sub with const*P
            let w0 := calldataload(ptr)
            let w1 := calldataload(add(ptr, 32))
            let c0 := shr(128, w0)
            let c1 := and(w0, MASK)
            let c2 := shr(128, w1)
            let c3 := and(w1, MASK)
            let g0g1 := add(add(add(add(c0, c0), c1), c2), c3)
            // r drawn before the claim check on purpose — optimal for the packed dual
            // family on solc (plain non-packed is the opposite; see HEURISTICS.md).
            let r := transcript_4to1_dual(w0, w1)
            if mod(sub(add(claim, mul(6, P)), g0g1), P) { revert(0, 0) }
            // NB: the 17P variant is more gas-efficient
            // but it's risky to use until we have hand measured
            // the max overflow possible in any given circuit
            // for now, i leave it off. feel free to re-enable once measured
            // if mod(sub(add(g0g1, mul(17, P)), claim), P) { revert(0, 0) }
            next_claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
            next_ptr := add(ptr, 64)
        }

        function sumcheck_compress_2pass(ptr, claim, alpha, rounds_skiplast) -> next_ptr, next_claim, next_alpha {
            // START WITH LAYER: 2^4 poly -> 2^5 polys (last var skip)
            // let rounds_skiplast := 3 // keep this const for now
            let eq_scale := 1
            // TODO: can offload alpha to memory bc it's used only in the end
            for { let i := 0 } lt(i, rounds_skiplast) { i := add(i, 1) } {
                // ptr, claim := sumcheck_round_dual(ptr, claim)
                let w0 := calldataload(ptr)
                let w1 := calldataload(add(ptr, 32))
                let c0 := shr(128, w0)
                let c1 := and(w0, MASK)
                let c2 := shr(128, w1)
                let c3 := and(w1, MASK)
                let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P)
                let r := transcript_4to1_dual(w0, w1) // before-check draw is intentional; see HEURISTICS.md
                // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
                if mod(add(claim, sub(P, g0g1_scaled)), P) { revert(0, 0) }
                claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
                let z := mload(add(POINT_PTR, mul(i, 32)))
                let zr := mulmod(z, r, P)
                eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
                mstore(add(POINT_PTR, mul(i, 32)), r)
                ptr := add(ptr, 64)
            }

            // POINT CHECK
            // TODO: this might need to be permuted in the last compression before circuit, due to prover shenanigans
            // ie. calldata slots are permuted vs batching order (real output addrs sort differently than group order):
            // walk [2,3,4,5,0,1,6,7] instead of [0..7] — circuit-specific, see DIM_REDUCE_INDICES_4.
            // The next-claim fold below is NOT affected (stays calldata order for all layers).
            let acc0 // RLC for x4 == 0
            for { let poly := 6 } gt(poly, 0) { poly := sub(poly, 2) } {
                // TODO: collect den0 and combine den_acc*alpha + num_acc as
                // d0 * (d1 * alpha + n1) + n0 * d1; revisit other logup paths too.
                let numbase := add(ptr, mul(poly, GKR_COMPRESSION_POINTCHECK_POLY_BYTES))
                let denbase := add(ptr, mul(add(poly, 1), GKR_COMPRESSION_POINTCHECK_POLY_BYTES))
                let denword := calldataload(denbase)

                let den0 := shr(128, denword)
                let den1 := and(MASK, denword)
                let den_acc := mulmod(den0, den1, P)
                acc0 := add(mulmod(acc0, alpha, P), den_acc)

                let numword := calldataload(numbase)
                let num0 := shr(128, numword)
                let num1 := and(MASK, numword)
                let num_acc := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                acc0 := add(mulmod(acc0, alpha, P), num_acc)
            }
            for { let poly := 1 } lt(poly, 2) { poly := sub(poly, 1) } {
                let base := add(ptr, mul(poly, GKR_COMPRESSION_POINTCHECK_POLY_BYTES))
                let word := calldataload(base)
                let prod0 := shr(128, word)
                let prod1 := and(MASK, word)
                let contribution := mulmod(prod0, prod1, P)
                acc0 := add(mulmod(acc0, alpha, P), contribution)
            }
            let acc1 // compute RLC for x4 == 1
            for { let poly := 6 } gt(poly, 0) { poly := sub(poly, 2) } {
                // TODO: collect den0 and combine den_acc*alpha + num_acc as
                // d0 * (d1 * alpha + n1) + n0 * d1; revisit other logup paths too.
                let numbase := add(ptr, mul(poly, GKR_COMPRESSION_POINTCHECK_POLY_BYTES))
                let denbase := add(ptr, mul(add(poly, 1), GKR_COMPRESSION_POINTCHECK_POLY_BYTES))
                let denword := calldataload(add(denbase, 32))

                let den0 := shr(128, denword)
                let den1 := and(MASK, denword)
                let den_acc := mulmod(den0, den1, P)
                acc1 := add(mulmod(acc1, alpha, P), den_acc)

                let numword := calldataload(add(numbase, 32))
                let num0 := shr(128, numword)
                let num1 := and(MASK, numword)
                let num_acc := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                acc1 := add(mulmod(acc1, alpha, P), num_acc)
            }
            for { let poly := 1 } lt(poly, 2) { poly := sub(poly, 1) } {
                let base := add(ptr, mul(poly, GKR_COMPRESSION_POINTCHECK_POLY_BYTES))
                let word := calldataload(add(base, 32))
                let prod0 := shr(128, word)
                let prod1 := and(MASK, word)
                let contribution := mulmod(prod0, prod1, P)
                acc1 := add(mulmod(acc1, alpha, P), contribution)
            }
            let diff := add(acc1, sub(mul(2, P), acc0))
            let z_last := mload(add(POINT_PTR, mul(rounds_skiplast, 32)))
            let rhs_scaled := mulmod(add(acc0, mulmod(z_last, diff, P)), eq_scale, P)
            // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
            if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }

            // POINT CLAIMS INTERPOLATE + BATCH
            // TODO: if compilation is good, try to merge this with POINTCHECK
            // remember to reset ptr back..
            let r_last, r_pair // ie. new (zN, zN+1) points
            r_last, r_pair, next_alpha := transcript32to3(ptr)
            mstore(add(POINT_PTR, mul(rounds_skiplast, 32)), r_last)
            mstore(add(POINT_PTR, mul(add(rounds_skiplast, 1), 32)), r_pair)
            for { let poly := 7 } lt(poly, 8) { poly := sub(poly, 1) } {
                let base := add(ptr, mul(poly, GKR_COMPRESSION_POINTCHECK_POLY_BYTES))

                let word0 := calldataload(base)
                let el0 := shr(128, word0)
                let el1 := and(MASK, word0)
                let claim0 := add(el0, mulmod(r_pair, add(el1, sub(mul(2, P), el0)), P))

                let word1 := calldataload(add(base, 32))
                let el2 := shr(128, word1)
                let el3 := and(MASK, word1)
                let claim1 := add(el2, mulmod(r_pair, add(el3, sub(mul(2, P), el2)), P))

                let poly_claim := add(claim0, mulmod(r_last, add(claim1, sub(mul(3, P), claim0)), P))
                next_claim := add(mulmod(next_claim, next_alpha, P), poly_claim)
            }

            next_ptr := add(ptr, GKR_COMPRESSION_POINTCHECK_BYTES)
        }


        function gkr_compress(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
            for { let layer_vars_skiplast := 3 } lt(layer_vars_skiplast, 23) { layer_vars_skiplast := add(layer_vars_skiplast, 1) } {
                ptr, claim, alpha := sumcheck_compress_2pass(ptr, claim, alpha, layer_vars_skiplast)
            }
            next_ptr := ptr
            next_claim := claim
            next_alpha := alpha
        }

        // __INLINE_CIRCUIT_YUL__

        function gkr_circuit(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
            ptr, claim, alpha := sumcheck_circuit_layer3(ptr, claim, alpha)
            ptr, claim, alpha := sumcheck_circuit_layer2(ptr, claim, alpha)
            ptr, claim, alpha := sumcheck_circuit_layer1(ptr, claim, alpha)
            ptr, claim, alpha := sumcheck_circuit_layer0(ptr, claim, alpha)
            next_ptr := ptr
            next_claim := claim
            next_alpha := alpha
        }

        // INIT MAIN
        // Stash starting gas to memory across the gkr_init_* call so that
        // Yul stack spills can't corrupt it under high register pressure.
        let ptr, claim, alpha
        {
            mstore(GKR_INIT_GAS_PTR, gas())
            mstore(SEED_PTR, 0) // SEED Transcript, FINE as long as we don't draw without absorb!
            ptr := transcript_init(0)
            ptr, claim, alpha := gkr_init_inlinefold(ptr)
            let init_gas := sub(mload(GKR_INIT_GAS_PTR), gas())
            mstore(GKR_INIT_GAS_PTR, init_gas)
        }

        // MAIN
        {
            mstore(GKR_COMPRESS_GAS_PTR, gas())
            ptr, claim, alpha := gkr_compress(ptr, claim, alpha)
            ptr, claim, alpha := gkr_circuit(ptr, claim, alpha)
            let compress_gas := sub(mload(GKR_COMPRESS_GAS_PTR), gas())
            mstore(GKR_COMPRESS_GAS_PTR, compress_gas)
        }

        // DONE: Proof empty now
        for { let i := 0 } lt(i, 10) { i := add(i, 1) } {
            if calldataload(add(ptr, mul(i, 32))) { revert(0, 0) }
        }

        // TODO: don't forget the recursion chain check

        // anti-DCE
        mstore(0, claim)
        mstore(32, mload(GKR_INIT_GAS_PTR))
        mstore(64, mload(GKR_COMPRESS_GAS_PTR))
        mstore(96, ptr)
        return(0, 128)
    } }
}

// Test/bench harness. Inherits GKRVerifier so it picks up the fallback (and
// ROUNDS) for free: `address(this).call(data)` invokes the inherited fallback
// exactly as a standalone GKRVerifier deployment would, so the measured gas
// reflects production. GKRVerifier itself stays free of test-only code, so
// `forge build --sizes` (and any prod build) sees only the verifier bytecode.
contract GKRVerifierTest is GKRVerifier {
    event log_named_uint(string key, uint256 val);
    event log_named_decimal_uint(string key, uint256 val, uint256 decimals);
    event log_named_string(string key, string val);

    function test() external {
        // Generation runs in a separate contract: GKRVerifierTest contains the
        // (memory-unsafe) verifier assembly, which disables the compilers'
        // stack-to-memory spilling for everything compiled into it. Keeping the
        // generator out of this contract means it can grow without ever
        // competing with the verifier for stack budget (solx no-spill etc).
        (bytes memory data, uint256 claim) = (new GKRStreamGen()).run(ROUNDS);
        emit log_named_uint("rounds",         ROUNDS);
        emit log_named_uint("calldata_bytes", data.length);
        emit log_named_uint("claim",          claim);
        emit log_named_uint("static_gas",     21000);
        bench_variant(0, data);
    }

    function bench_variant(uint256 variant, bytes memory data) internal {
        emit log_named_uint("",                variant);
        uint256 outer_gas_delta = gasleft();
        (bool ok, bytes memory ret) = address(this).call(data);
        outer_gas_delta -= gasleft();
        require(ok, "verify failed");
        (uint256 output_claim, uint256 init_gas, uint256 compress_gas, uint256 ptr) =
            abi.decode(ret, (uint256, uint256, uint256, uint256));
        output_claim;
        ptr;

        uint256 main_gas = init_gas + compress_gas;
        uint256 data_gas = calldata_gas(data, main_gas);
        uint256 total_gas = 21000 + data_gas + main_gas;
        emit log_named_uint("calldata_gas",   data_gas);
        emit log_named_string("init_gas",      gas_with_percent(init_gas, total_gas));
        emit log_named_string("compress_gas",  gas_with_percent(compress_gas, total_gas));
        // emit log_named_decimal_uint("gas/round", (compress_gas * 100) / ROUNDS, 2);
        // emit log_named_uint("outer_gas_delta", outer_gas_delta);
        emit log_named_string("main_gas",      gas_with_percent(main_gas, total_gas));
    }
}

function calldata_gas(bytes memory data, uint256 execution_gas) pure returns (uint256) {
    uint256 standard = 0;
    uint256 pectra_eip7623_tokens = 0;
    for (uint256 i = 0; i < data.length; ++i) {
        if (data[i] == 0) {
            standard += 4;
            pectra_eip7623_tokens += 1;
        } else {
            standard += 16;
            pectra_eip7623_tokens += 4;
        }
    }
    uint256 pectra_eip7623 = 10 * pectra_eip7623_tokens;
    uint256 execution_with_standard_data = execution_gas + standard;
    return execution_with_standard_data > pectra_eip7623
        ? standard
        : pectra_eip7623 - execution_gas;
}

function gas_with_percent(uint256 value, uint256 total) pure returns (string memory) {
    uint256 percent = total == 0 ? 0 : (value * 100 + total - 1) / total;
    return string.concat(uint_to_string(value), " (", uint_to_string(percent), "%)");
}

function uint_to_string(uint256 value) pure returns (string memory) {
    if (value == 0) {
        return "0";
    }

    uint256 digits = 0;
    uint256 tmp = value;
    while (tmp != 0) {
        digits++;
        tmp /= 10;
    }

    bytes memory buffer = new bytes(digits);
    while (value != 0) {
        digits--;
        // value % 10 ∈ [0, 9], so 48 + value % 10 ∈ [48, 57] — fits in uint8.
        // forge-lint: disable-next-line(unsafe-typecast)
        buffer[digits] = bytes1(uint8(48 + value % 10));
        value /= 10;
    }
    return string(buffer);
}

// Stream generator wrapper. Free functions below compile into THIS contract
// only (no assembly here), so spilling is available and stack-too-deep is a
// non-issue however large the generator gets. Replaced by Rust later.
contract GKRStreamGen {
    function run(uint256 numvars) external pure returns (bytes memory out, uint256 initial_claim) {
        return generate(numvars);
    }
}

// Build a valid prototype stream:
// Values are serialized in logical stream order with fixed-width big-endian bytes:
// Rust push(u32/u64/u128) appends x.to_be_bytes(), and hashes append raw bytes.
// For u128 pairs this means [x0:16][x1:16], decoded as x0=shr(128, word), x1=low.
// Sumcheck rounds are [c0:16][c1:16][c2:16][c3:16].
// Init transcript mirrors transcript128to5_once with an all-zero initial seed:
// state := keccak256(bytes32(0) || init), then two more state-only hashes to
// draw z1..z4 and alpha. Sumcheck rounds continue from the post-alpha state.
// After the rounds, a single compression layer follows: 3 eq-deferred round
// word-pairs, then the 512-byte pointcheck blob (8 polys x 2 words).
function modInv(uint256 x, uint256 p) pure returns (uint256 result) {
    // Fermat: x^(p-2) mod p, via square-and-multiply.
    uint256 exp = p - 2;
    uint256 base = x % p;
    result = 1;
    while (exp != 0) {
        if (exp & 1 == 1) {
            result = mulmod(result, base, p);
        }
        base = mulmod(base, base, p);
        exp >>= 1;
    }
}

function generate_init_transcript_caps(bytes32 coeff_seed)
    pure
    returns (bytes memory capsData, bytes32 state, uint256 logupAlpha, uint256 logupGamma)
{
    bytes memory memCaps;
    bytes memory witSetupCaps;

    for (uint256 i = 0; i < 16; ++i) {
        memCaps = abi.encodePacked(memCaps, keccak256(abi.encodePacked(coeff_seed, "mem-cap", i)));
    }
    for (uint256 i = 0; i < 16; ++i) {
        witSetupCaps = abi.encodePacked(witSetupCaps, keccak256(abi.encodePacked(coeff_seed, "witness-cap", i)));
    }
    for (uint256 i = 0; i < 16; ++i) {
        witSetupCaps = abi.encodePacked(witSetupCaps, keccak256(abi.encodePacked(coeff_seed, "setup-cap", i)));
    }

    state = keccak256(abi.encodePacked(bytes32(0), memCaps));
    state = keccak256(abi.encodePacked(state));
    state = keccak256(abi.encodePacked(state));
    state = keccak256(abi.encodePacked(state));
    state = keccak256(abi.encodePacked(state, witSetupCaps));
    logupAlpha = uint256(state) >> 128;
    logupGamma = uint128(uint256(state));
    capsData = abi.encodePacked(memCaps, witSetupCaps);
}

function generate(uint256) pure returns (bytes memory out, uint256 initial_claim) {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    uint256 initFieldElements = 8 * 16;
    uint256 initPolySize = 16;
    bytes32 coeff_seed = keccak256("gkr_claude_seed");
    (bytes memory capsData, bytes32 state, uint256 logupAlpha, uint256 logupGamma) =
        generate_init_transcript_caps(coeff_seed);
    uint128[] memory initEvals = new uint128[](initFieldElements);
    bytes memory initData = new bytes(initFieldElements * 16);

    for (uint256 i = 0; i < initFieldElements; ++i) {
        // (... % p) < p < 2^128 — fits in uint128.
        // forge-lint: disable-next-line(unsafe-typecast)
        initEvals[i] = uint128(uint256(keccak256(abi.encodePacked(coeff_seed, uint8(0), i))) % p);
    }

    // Patch write[15] so ∏read == ∏write (grand-product check).
    {
        uint256 readProd = 1;
        for (uint256 i = 0; i < 16; ++i) {
            readProd = mulmod(readProd, uint256(initEvals[i]), p);
        }
        uint256 writePartial = 1;
        for (uint256 i = 16; i < 31; ++i) {
            writePartial = mulmod(writePartial, uint256(initEvals[i]), p);
        }
        initEvals[31] = uint128(mulmod(readProd, modInv(writePartial, p), p));
    }

    // Patch num[15] of each logup pair so ∑ num_i/den_i == 0.
    // Polys: [num=2,den=3], [num=4,den=5], [num=6,den=7]; each poly is 16 elements.
    for (uint256 k = 0; k < 3; ++k) {
        uint256 numBase = 32 + k * 32;
        uint256 denBase = numBase + 16;
        uint256 pn = 0;
        uint256 pd = 1;
        for (uint256 i = 0; i < 15; ++i) {
            uint256 n = uint256(initEvals[numBase + i]);
            uint256 d = uint256(initEvals[denBase + i]);
            pn = addmod(mulmod(pn, d, p), mulmod(n, pd, p), p);
            pd = mulmod(pd, d, p);
        }
        uint256 d15 = uint256(initEvals[denBase + 15]);
        uint256 nv = mulmod(mulmod(pn, d15, p), modInv(pd, p), p);
        // (... % p) < p < 2^128 — fits in uint128.
        // forge-lint: disable-next-line(unsafe-typecast)
        initEvals[numBase + 15] = uint128((p - nv) % p);
    }

    // Serialize patched evals to big-endian 16-byte field elements.
    for (uint256 i = 0; i < initFieldElements; ++i) {
        uint256 offset = i * 16;
        uint256 elWord = uint256(initEvals[i]);
        for (uint256 j = 0; j < 16; ++j) {
            // elWord >> (8 * (15 - j)) takes one byte — masked to uint8 by the cast.
            // forge-lint: disable-next-line(unsafe-typecast)
            initData[offset + j] = bytes1(uint8(elWord >> (8 * (15 - j))));
        }
    }

    state = keccak256(abi.encodePacked(state, initData));
    uint256 z1 = uint256(state) >> 128;
    uint256 z2 = uint128(uint256(state));

    state = keccak256(abi.encodePacked(state));
    uint256 z3 = uint256(state) >> 128;
    uint256 z4 = uint128(uint256(state));

    state = keccak256(abi.encodePacked(state));
    uint256 alpha = uint256(state) >> 128;
    // Stash the point in memory immediately: keeping z1..z4 alive on the
    // stack until the generate_compression calls below blows the stack
    // budget of the later loops (solx no-spill / solc no_rematerializer).
    // 24 coords: starts at 4 (init), each compression layer appends 2 and
    // re-binds the rest, ending at claims on 2^24-sized polys.
    uint256[24] memory zpoint;
    zpoint[0] = z1;
    zpoint[1] = z2;
    zpoint[2] = z3;
    zpoint[3] = z4;

    uint256 p34 = mulmod(z3, z4, p);
    uint256[4] memory eq34;
    eq34[0] = addmod(addmod(1, p34, p), p - addmod(z3 % p, z4 % p, p), p);
    eq34[1] = addmod(z4 % p, p - p34, p);
    eq34[2] = addmod(z3 % p, p - p34, p);
    eq34[3] = p34;

    uint256 p12 = mulmod(z1, z2, p);
    uint256[4] memory eq12;
    eq12[0] = addmod(addmod(1, p12, p), p - addmod(z1 % p, z2 % p, p), p);
    eq12[1] = addmod(z2 % p, p - p12, p);
    eq12[2] = addmod(z1 % p, p - p12, p);
    eq12[3] = p12;

    // Per-poly partial claim: dot(eq, poly_evals). Then Horner-fold with alpha.
    uint256[8] memory partials;
    for (uint256 k = 0; k < 8; ++k) {
        uint256 s = 0;
        for (uint256 i = 0; i < initPolySize; ++i) {
            uint256 eq = mulmod(eq12[i >> 2], eq34[i & 3], p);
            s = addmod(s, mulmod(uint256(initEvals[k * initPolySize + i]), eq, p), p);
        }
        partials[k] = s;
    }
    uint256 claim = partials[7];
    for (uint256 k = 7; k > 0; --k) {
        claim = addmod(partials[k - 1], mulmod(claim, alpha, p), p);
    }
    initial_claim = claim;

    out = abi.encodePacked(capsData, initData);

    // Placeholder main sumcheck rounds disabled: compress now starts directly
    // from the 2^4 plaintext polys produced by init.
    // for (uint256 i = 0; i < numvars; i++) {
    //     uint128 c1 = uint128(uint256(keccak256(abi.encodePacked(coeff_seed, i, uint8(1)))));
    //     uint128 c2 = uint128(uint256(keccak256(abi.encodePacked(coeff_seed, i, uint8(2)))));
    //     uint128 c3 = uint128(uint256(keccak256(abi.encodePacked(coeff_seed, i, uint8(3)))));
    //
    //     uint256 rhs = claim;
    //     rhs = addmod(rhs, p - (uint256(c1) % p), p);
    //     rhs = addmod(rhs, p - (uint256(c2) % p), p);
    //     rhs = addmod(rhs, p - (uint256(c3) % p), p);
    //     uint128 c0 = uint128(mulmod(rhs, inv2, p));
    //
    //     out = abi.encodePacked(out, c0, c1, c2, c3);
    //
    //     state = keccak256(abi.encodePacked(state, c0, c1, c2, c3));
    //     uint256 r = uint256(state) >> 128;
    //
    //     uint256 t = mulmod(uint256(c3), r, p);
    //     t = addmod(t, uint256(c2), p);
    //     t = mulmod(t, r, p);
    //     t = addmod(t, uint256(c1), p);
    //     t = mulmod(t, r, p);
    //     claim = addmod(t, uint256(c0), p);
    // }

    out = generate_after_init(out, state, claim, alpha, zpoint, coeff_seed, logupAlpha, logupGamma);
}

function generate_after_init(
    bytes memory out,
    bytes32 state,
    uint256 claim,
    uint256 alpha,
    uint256[24] memory zpoint,
    bytes32 coeff_seed,
    uint256 logupAlpha,
    uint256 logupGamma
) pure returns (bytes memory) {
    for (uint256 layer = 0; layer < 20; ++layer) {
        (out, state, claim, alpha) = generate_compression(
            out, state, claim, alpha, zpoint, keccak256(abi.encodePacked(coeff_seed, layer)), 3 + layer
        );
    }

    (out, state, claim, alpha) = generate_circuit_layer(
        out, state, claim, alpha, zpoint, keccak256(abi.encodePacked(coeff_seed, "circuit-layer-3")), 3, 16,
        logupAlpha, logupGamma
    );
    (out, state, claim, alpha) = generate_circuit_layer(
        out, state, claim, alpha, zpoint, keccak256(abi.encodePacked(coeff_seed, "circuit-layer-2")), 2, 25,
        logupAlpha, logupGamma
    );
    (out, state, claim, alpha) = generate_circuit_layer(
        out, state, claim, alpha, zpoint, keccak256(abi.encodePacked(coeff_seed, "circuit-layer-1")), 1, 72,
        logupAlpha, logupGamma
    );
    state;
    claim;
    alpha;
    return out;
}

// === Compression layer generator (mirrors gkr_compress_2pass) ===
// `rounds` eq-deferred rounds, then an 8-poly pointcheck blob (2 products at
// calldata 0,1 + 3 logup num/den pairs at (2,3),(4,5),(6,7); per poly
// [x4=0 word | x4=1 word], halves [pair=0 | pair=1]). Product poly 0's
// (x4=0, pair=0) eval is solved so the final point check passes.
// The point enters with (rounds + 1) live coords; rounds re-bind coords
// [0..rounds), the check folds by coord [rounds], and the two fresh draws
// land at [rounds] and [rounds + 1] — all mirrored into zpoint in place.
// coeff_seed should be unique per layer (generate() derives one per call).
// Lives in its own function frame: the inherited verifier assembly has no
// memoryguard, so via-ir cannot spill generate()'s stack to memory.
function generate_compression(
    bytes memory out,
    bytes32 state,
    uint256 claim,
    uint256 alpha,
    uint256[24] memory zpoint,
    bytes32 coeff_seed,
    uint256 rounds
) pure returns (bytes memory, bytes32, uint256, uint256) {
    uint256 p = 0xffffffffffffffffffffffffffffff61;

    uint256 eq_scale = 1;
    for (uint256 i = 0; i < rounds; i++) {
        uint128 c1 = uint128(uint256(keccak256(abi.encodePacked(coeff_seed, i, uint8(4)))));
        uint128 c2 = uint128(uint256(keccak256(abi.encodePacked(coeff_seed, i, uint8(5)))));
        uint128 c3 = uint128(uint256(keccak256(abi.encodePacked(coeff_seed, i, uint8(6)))));

        // Solve c0 from (2*c0 + c1 + c2 + c3) * eq_scale == claim.
        uint256 rhs = mulmod(claim, modInv(eq_scale, p), p);
        rhs = addmod(rhs, p - (uint256(c1) % p), p);
        rhs = addmod(rhs, p - (uint256(c2) % p), p);
        rhs = addmod(rhs, p - (uint256(c3) % p), p);
        // inv2 = (p >> 1) + 1; (... % p) < p < 2^128 — fits in uint128.
        // forge-lint: disable-next-line(unsafe-typecast)
        uint128 c0 = uint128(mulmod(rhs, (p >> 1) + 1, p));

        out = abi.encodePacked(out, c0, c1, c2, c3);

        // absorb 4 coeffs, squeeze low 128 bits as r
        state = keccak256(abi.encodePacked(state, c0, c1, c2, c3));
        uint256 r = uint256(state) >> 128;

        uint256 t = mulmod(uint256(c3), r, p);
        t = addmod(t, uint256(c2), p);
        t = mulmod(t, r, p);
        t = addmod(t, uint256(c1), p);
        t = mulmod(t, r, p);
        claim = addmod(t, uint256(c0), p);

        // eq_scale = eq(z_i, r) = 2*z*r + 1 - z - r
        uint256 z = zpoint[i] % p;
        uint256 zr = mulmod(z, r, p);
        eq_scale = addmod(addmod(addmod(zr, zr, p), 1, p), p - addmod(z, r % p, p), p);
        zpoint[i] = r;
    }

    // Pointcheck evals: evs[poly*4 + 2*x4 + pair], canonical.
    uint128[32] memory evs;
    for (uint256 i = 0; i < 32; ++i) {
        // (... % p) < p < 2^128 — fits in uint128.
        // forge-lint: disable-next-line(unsafe-typecast)
        evs[i] = uint128(uint256(keccak256(abi.encodePacked(coeff_seed, uint8(7), i))) % p);
    }

    // RLCs in verifier walk order; x4 selects the word (0 or 1). acc0 stops
    // before poly 0 (patched below), so its poly-0 step is skipped here and
    // applied by the patch block.
    uint256 acc0 = pointcheck_rlc(evs, alpha, 0, true);
    uint256 acc1 = pointcheck_rlc(evs, alpha, 1, false);

    // Solve acc0 from (acc0*(1-z4) + acc1*z4) * eq_scale == claim, then
    // patch evs[0] so poly 0's product contribution lands exactly there.
    {
        uint256 z4r = zpoint[rounds] % p;
        uint256 target = mulmod(claim, modInv(eq_scale, p), p);
        target = addmod(target, p - mulmod(acc1, z4r, p), p);
        target = mulmod(target, modInv(addmod(1, p - z4r, p), p), p);
        uint256 needed = addmod(target, p - mulmod(acc0, alpha, p), p);
        if (evs[1] == 0) evs[1] = 1;
        // (... % p) < p < 2^128 — fits in uint128.
        // forge-lint: disable-next-line(unsafe-typecast)
        evs[0] = uint128(mulmod(needed, modInv(uint256(evs[1]), p), p));
    }

    // Serialize the 512-byte blob (poly-major, big-endian 16-byte halves),
    // append, and absorb: transcript32to3 hashes seed || blob in one shot.
    {
        bytes memory blob = new bytes(512);
        for (uint256 i = 0; i < 32; ++i) {
            uint256 offset = i * 16;
            uint256 elWord = uint256(evs[i]);
            for (uint256 j = 0; j < 16; ++j) {
                // elWord >> (8 * (15 - j)) takes one byte — masked to uint8 by the cast.
                // forge-lint: disable-next-line(unsafe-typecast)
                blob[offset + j] = bytes1(uint8(elWord >> (8 * (15 - j))));
            }
        }
        out = abi.encodePacked(out, blob);
        state = keccak256(abi.encodePacked(state, blob));
    }

    // Draws: (r_last | r_pair) from the absorb, then the next batching alpha.
    uint256 r_last = uint256(state) >> 128;
    uint256 r_pair = uint128(uint256(state));
    state = keccak256(abi.encodePacked(state));
    alpha = uint256(state) >> 128;
    zpoint[rounds] = r_last;
    zpoint[rounds + 1] = r_pair;

    // Fold next-layer claims (poly 7 -> 0 Horner, calldata order) so the
    // returned claim/alpha stay correct for chaining more layers.
    claim = fold_pointcheck_claims(evs, r_last, r_pair, alpha);

    return (out, state, claim, alpha);
}

// === Circuit layer generator (mirrors sumcheck_circuit_layer3/2) ===
// This is deliberately mock-only: it solves the streamed proof equations for
// the generated layer Yul without attempting to derive values from SSA witness
// generation. The real prover should replace it.
function generate_circuit_layer(
    bytes memory out,
    bytes32 state,
    uint256 claim,
    uint256 alpha,
    uint256[24] memory zpoint,
    bytes32 coeff_seed,
    uint256 layer,
    uint256 points,
    uint256 logupAlpha,
    uint256 logupGamma
) pure returns (bytes memory, bytes32, uint256, uint256) {
    uint256 eq_scale;
    (out, state, claim, eq_scale) = generate_circuit_sumcheck(out, state, claim, zpoint, coeff_seed);
    uint256[] memory vals = generate_circuit_points(
        coeff_seed,
        points,
        layer,
        alpha,
        logupAlpha,
        logupGamma,
        mulmod(claim, modInv(eq_scale, 0xffffffffffffffffffffffffffffff61), 0xffffffffffffffffffffffffffffff61)
    );
    bytes memory pointData = serialize_u128s(vals);
    out = abi.encodePacked(out, pointData);
    state = keccak256(abi.encodePacked(state, pointData));
    alpha = uint256(state) >> 128;
    claim = fold_claims(vals, alpha);

    return (out, state, claim, alpha);
}

function generate_circuit_sumcheck(
    bytes memory out,
    bytes32 state,
    uint256 claim,
    uint256[24] memory zpoint,
    bytes32 coeff_seed
) pure returns (bytes memory, bytes32, uint256, uint256) {
    uint256 eq_scale = 1;
    for (uint256 i = 0; i < 24; ++i) {
        (out, state, claim, eq_scale) = generate_circuit_round(out, state, claim, eq_scale, zpoint, coeff_seed, i);
    }
    return (out, state, claim, eq_scale);
}

function generate_circuit_round(
    bytes memory out,
    bytes32 state,
    uint256 claim,
    uint256 eq_scale,
    uint256[24] memory zpoint,
    bytes32 coeff_seed,
    uint256 i
) pure returns (bytes memory, bytes32, uint256, uint256) {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    // (... % p) < p < 2^128 — fits in uint128.
    // forge-lint: disable-next-line(unsafe-typecast)
    uint128 c1 = uint128(uint256(keccak256(abi.encodePacked(coeff_seed, i, uint8(1)))) % p);
    // (... % p) < p < 2^128 — fits in uint128.
    // forge-lint: disable-next-line(unsafe-typecast)
    uint128 c2 = uint128(uint256(keccak256(abi.encodePacked(coeff_seed, i, uint8(2)))) % p);
    // (... % p) < p < 2^128 — fits in uint128.
    // forge-lint: disable-next-line(unsafe-typecast)
    uint128 c3 = uint128(uint256(keccak256(abi.encodePacked(coeff_seed, i, uint8(3)))) % p);
    uint128 c0 = solve_sumcheck_c0(claim, eq_scale, c1, c2, c3);

    out = abi.encodePacked(out, c0, c1, c2, c3);
    state = keccak256(abi.encodePacked(state, c0, c1, c2, c3));
    uint256 r = uint256(state) >> 128;
    claim = eval_sumcheck_at_r(c0, c1, c2, c3, r);
    eq_scale = next_eq_scale(zpoint[i], r);
    zpoint[i] = r;
    return (out, state, claim, eq_scale);
}

function solve_sumcheck_c0(uint256 claim, uint256 eq_scale, uint128 c1, uint128 c2, uint128 c3)
    pure
    returns (uint128)
{
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    uint256 rhs = mulmod(claim, modInv(eq_scale, p), p);
    rhs = addmod(rhs, p - uint256(c1), p);
    rhs = addmod(rhs, p - uint256(c2), p);
    rhs = addmod(rhs, p - uint256(c3), p);
    return uint128(mulmod(rhs, (p >> 1) + 1, p));
}

function eval_sumcheck_at_r(uint128 c0, uint128 c1, uint128 c2, uint128 c3, uint256 r)
    pure
    returns (uint256)
{
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    uint256 t = mulmod(uint256(c3), r, p);
    t = addmod(t, uint256(c2), p);
    t = mulmod(t, r, p);
    t = addmod(t, uint256(c1), p);
    t = mulmod(t, r, p);
    return addmod(t, uint256(c0), p);
}

function next_eq_scale(uint256 z, uint256 r) pure returns (uint256) {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    z %= p;
    uint256 zr = mulmod(z, r, p);
    return addmod(addmod(addmod(zr, zr, p), 1, p), p - addmod(z, r % p, p), p);
}

function generate_circuit_points(
    bytes32 coeff_seed,
    uint256 points,
    uint256 layer,
    uint256 alpha,
    uint256 logupAlpha,
    uint256 logupGamma,
    uint256 target
) pure returns (uint256[] memory vals) {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    vals = new uint256[](points);
    for (uint256 i = 0; i < points; ++i) {
        vals[i] = uint256(keccak256(abi.encodePacked(coeff_seed, uint8(4), i))) % p;
    }
    patch_circuit_pointcheck(vals, layer, alpha, logupAlpha, logupGamma, target);
}

function patch_circuit_pointcheck(
    uint256[] memory vals,
    uint256 layer,
    uint256 alpha,
    uint256 logupAlpha,
    uint256 logupGamma,
    uint256 target
) pure {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    if (layer == 3) {
        vals[15] = 0;
        uint256 rest = circuit_layer3_acc(vals, alpha);
        vals[15] = mulmod(addmod(target, p - rest, p), modInv(pow_mod(alpha, 9, p), p), p);
    } else if (layer == 2) {
        vals[24] = 0;
        uint256 rest = circuit_layer2_acc(vals, alpha);
        vals[24] = mulmod(addmod(target, p - rest, p), modInv(pow_mod(alpha, 15, p), p), p);
    } else {
        vals[0] = 0;
        uint256 rest = circuit_layer1_acc(vals, alpha, logupAlpha, logupGamma);
        vals[0] = addmod(target, p - rest, p);
    }
}

function circuit_layer3_acc(uint256[] memory v, uint256 alpha) pure returns (uint256 acc) {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    acc = addmod(mulmod(acc, alpha, p), v[15], p);
    acc = addmod(mulmod(acc, alpha, p), v[14], p);
    acc = addmod(mulmod(acc, alpha, p), v[1], p);
    acc = addmod(mulmod(acc, alpha, p), v[0], p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[13], v[11], p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[12], v[11], p), mulmod(v[10], v[13], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[9], v[7], p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[8], v[7], p), mulmod(v[6], v[9], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[5], v[3], p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[4], v[3], p), mulmod(v[2], v[5], p), p), p);
}

function circuit_layer2_acc(uint256[] memory v, uint256 alpha) pure returns (uint256 acc) {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    acc = addmod(mulmod(acc, alpha, p), v[24], p);
    acc = addmod(mulmod(acc, alpha, p), v[23], p);
    acc = addmod(mulmod(acc, alpha, p), v[18], p);
    acc = addmod(mulmod(acc, alpha, p), v[17], p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[22], v[20], p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[21], v[20], p), mulmod(v[19], v[22], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), v[12], p);
    acc = addmod(mulmod(acc, alpha, p), v[11], p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[16], v[14], p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[15], v[14], p), mulmod(v[13], v[16], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[6], v[4], p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[5], v[4], p), mulmod(v[3], v[6], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[10], v[8], p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[9], v[8], p), mulmod(v[7], v[10], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[2], v[0], p), addmod(1, p - v[0], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[1], v[0], p), addmod(1, p - v[0], p), p), p);
}

function circuit_layer1_acc(uint256[] memory v, uint256 alpha, uint256 logupAlpha, uint256 logupGamma)
    pure
    returns (uint256 acc)
{
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    uint256 den1;
    uint256 den2;
    acc = addmod(mulmod(acc, alpha, p), v[5], p);
    acc = addmod(mulmod(acc, alpha, p), v[6], p);

    den2 = logup_vec(v, logupAlpha, logupGamma, [uint256(39), NO_POINT(), 47, 46, 45, 44, 43, 42, 41, 40]);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[71], den2, p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[70], den2, p), v[71], p), p);

    den1 = logup_vec(v, logupAlpha, logupGamma, [uint256(21), NO_POINT(), 29, 28, 27, 26, 25, 24, 23, 22]);
    den2 = logup_vec(v, logupAlpha, logupGamma, [uint256(30), NO_POINT(), 38, 37, 36, 35, 34, 33, 32, 31]);
    acc = addmod(mulmod(acc, alpha, p), mulmod(den1, den2, p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(den1, den2, p), p);

    den1 = logup_vec(v, logupAlpha, logupGamma, [uint256(8), NO_POINT(), NO_POINT(), NO_POINT(), NO_POINT(), NO_POINT(), NO_POINT(), 11, 10, 9]);
    den2 = logup_vec(v, logupAlpha, logupGamma, [uint256(12), NO_POINT(), 20, 19, 18, 17, 16, 15, 14, 13]);
    acc = addmod(mulmod(acc, alpha, p), mulmod(den1, den2, p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(den1, den2, p), p);

    acc = addmod(mulmod(acc, alpha, p), v[62], p);
    acc = addmod(mulmod(acc, alpha, p), v[61], p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[66], v[64], p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[65], v[64], p), mulmod(v[63], v[66], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[68], addmod(logupGamma, v[69], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[67], addmod(logupGamma, v[69], p), p), v[68], p), p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[49], addmod(logupGamma, v[7], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[48], addmod(logupGamma, v[7], p), p), v[49], p), p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[53], v[51], p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[52], v[51], p), mulmod(v[50], v[53], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[57], v[55], p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[56], v[55], p), mulmod(v[54], v[57], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[59], addmod(logupGamma, v[60], p), p), p);
    acc = addmod(mulmod(acc, alpha, p), addmod(mulmod(v[58], addmod(logupGamma, v[60], p), p), v[59], p), p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[2], v[4], p), p);
    acc = addmod(mulmod(acc, alpha, p), mulmod(v[1], v[3], p), p);
    acc = addmod(mulmod(acc, alpha, p), v[0], p);
}

function NO_POINT() pure returns (uint256) {
    return type(uint256).max;
}

function logup_vec(uint256[] memory v, uint256 beta, uint256 gamma, uint256[10] memory columns)
    pure
    returns (uint256 acc)
{
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    for (uint256 i = 0; i < 10; ++i) {
        acc = mulmod(acc, beta, p);
        if (columns[i] != NO_POINT()) {
            acc = addmod(acc, v[columns[i]], p);
        }
    }
    acc = addmod(acc, gamma, p);
}

function serialize_u128s(uint256[] memory vals) pure returns (bytes memory out) {
    out = new bytes(vals.length * 16);
    for (uint256 i = 0; i < vals.length; ++i) {
        uint256 offset = i * 16;
        uint256 elWord = vals[i];
        for (uint256 j = 0; j < 16; ++j) {
            // elWord >> (8 * (15 - j)) takes one byte — masked to uint8 by the cast.
            // forge-lint: disable-next-line(unsafe-typecast)
            out[offset + j] = bytes1(uint8(elWord >> (8 * (15 - j))));
        }
    }
}

function fold_claims(uint256[] memory vals, uint256 alpha) pure returns (uint256 claim) {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    for (uint256 i = vals.length; i > 0; --i) {
        claim = addmod(mulmod(claim, alpha, p), vals[i - 1], p);
    }
}

function pow_mod(uint256 base, uint256 exp, uint256 p) pure returns (uint256 result) {
    result = 1;
    base %= p;
    while (exp != 0) {
        if (exp & 1 == 1) {
            result = mulmod(result, base, p);
        }
        base = mulmod(base, base, p);
        exp >>= 1;
    }
}

// RLC of the pointcheck evals at x4 (word select): logup pairs (6,7),(4,5),
// (2,3) — den then num — then products 1, 0. skip_poly0 leaves out the last
// step so the caller can solve poly 0's contribution.
function pointcheck_rlc(uint128[32] memory evs, uint256 alpha, uint256 x4, bool skip_poly0)
    pure
    returns (uint256 acc)
{
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    uint256 w = 2 * x4;
    for (uint256 k = 0; k < 3; ++k) {
        uint256 nb = (6 - 2 * k) * 4 + w;
        uint256 db = nb + 4;
        acc = addmod(mulmod(acc, alpha, p), mulmod(uint256(evs[db]), uint256(evs[db + 1]), p), p);
        acc = addmod(
            mulmod(acc, alpha, p),
            addmod(
                mulmod(uint256(evs[nb]), uint256(evs[db + 1]), p),
                mulmod(uint256(evs[nb + 1]), uint256(evs[db]), p),
                p
            ),
            p
        );
    }
    acc = addmod(mulmod(acc, alpha, p), mulmod(uint256(evs[4 + w]), uint256(evs[5 + w]), p), p);
    if (!skip_poly0) {
        acc = addmod(mulmod(acc, alpha, p), mulmod(uint256(evs[w]), uint256(evs[1 + w]), p), p);
    }
}

// Bilinear-fold each poly's 4 evals at (r_last, r_pair) and Horner-batch
// (poly 7 -> 0, calldata order) with alpha.
function fold_pointcheck_claims(uint128[32] memory evs, uint256 r_last, uint256 r_pair, uint256 alpha)
    pure
    returns (uint256 claim)
{
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    for (uint256 poly = 8; poly > 0; --poly) {
        uint256 b = (poly - 1) * 4;
        uint256 cl0 = addmod(
            uint256(evs[b]),
            mulmod(r_pair, addmod(uint256(evs[b + 1]), p - uint256(evs[b]), p), p),
            p
        );
        uint256 cl1 = addmod(
            uint256(evs[b + 2]),
            mulmod(r_pair, addmod(uint256(evs[b + 3]), p - uint256(evs[b + 2]), p), p),
            p
        );
        uint256 pc = addmod(cl0, mulmod(r_last, addmod(cl1, p - cl0, p), p), p);
        claim = addmod(mulmod(claim, alpha, p), pc, p);
    }
}
