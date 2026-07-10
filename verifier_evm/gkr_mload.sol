// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.24;

contract GKRVerifier {
    // ── Generic (used throughout) ───────────────────────────────────────────
    // HEAP ORDER: challenges, point, gas, seed, init/circuit data (overlapping seed+32)
    // MEMORY_CHALLS_PTR (7)
    // LOGUP_CHALLS_PTR (2)
    // POINT_PTR (24)
    // GKR_INIT_GAS_PTR (1)
    // GKR_MAIN_GAS_PTR (1)
    // SEED_PTR (1)
    // optional SEED_PTR + 32:
    //    GKR_INIT/CIRCUIT 1 (1)
    //    GKR_INIT/CIRCUIT 2 (1)
    //    ..
    uint256 constant MINIMUM_FREE_HEAP_PTR = 11500;// 10560; // 7488;
    uint256 constant P_VALUE      = 0xffffffffffffffffffffffffffffff61; // 2^128 - 159
    uint256 constant MASK_VALUE   = 0xffffffffffffffffffffffffffffffff; // high 128 bits
    uint256 constant ROUNDS = 200;

    // ── Transcript init (absorb caps, derive memory/logup challenges) ─────────
    uint256 constant MERKLE_TREE_CAPS_BYTES = 512; // 16 caps * 32-byte hash

    // ── GKR init (fold the 8 init polys into the first sumcheck claim) ────────
    uint256 constant GKR_INIT_BYTES          = 2048; // 8 polys * 16 elems * 16 bytes
    uint256 constant GKR_INIT_POLY_BYTES     = 256;  // 16 elems * 16 bytes (literal; Yul rejects const exprs)

    // ── GKR compression ───────────────────────────────────────────────────────
    uint256 constant GKR_COMPRESSION_POINTCHECK_POLY_BYTES = 64;  // 4 * 16
    uint256 constant GKR_COMPRESSION_POINTCHECK_BYTES      = 512; // 8 * 64

    // ── GKR circuit ───────────────────────────────────────────────────────────
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

        function MEMORY_CHALLS_PTR() -> ptr {
            ptr := MINIMUM_FREE_HEAP_PTR
        }
        function LOGUP_CHALLS_PTR() -> ptr {
            ptr := add(MEMORY_CHALLS_PTR(), mul(32, 7))
        }
        function POINT_PTR() -> ptr {
            ptr := add(LOGUP_CHALLS_PTR(), mul(32, 2))
        }
        function GKR_INIT_GAS_PTR() -> ptr {
            ptr := add(POINT_PTR(), mul(32, GKR_CIRCUIT_LAYER_ROUNDS))
        }
        function GKR_MAIN_GAS_PTR() -> ptr {
            ptr := add(GKR_INIT_GAS_PTR(), mul(32, 1))
        }
        function P_PTR() -> ptr {
            ptr := add(GKR_MAIN_GAS_PTR(), mul(32, 1))
        }
        function MASK_PTR() -> ptr {
            ptr := add(P_PTR(), mul(32, 1))
        }
        function SEED_PTR() -> ptr {
            ptr := add(MASK_PTR(), mul(32, 1))
        }
        function GKR_INIT_SCRATCH_PTR() -> ptr {
            ptr := add(SEED_PTR(), mul(32, 1))
        }
        function GKR_INIT_CLAIM_PTR() -> ptr {
            ptr := add(SEED_PTR(), mul(32, 2))
        }
        function GKR_CIRCUIT_ALPHA2_PTR() -> ptr {
            ptr := add(SEED_PTR(), mul(32, 1))
        }
        function GKR_CIRCUIT_CACHE_PTR() -> ptr {
            ptr := add(SEED_PTR(), mul(32, 2))
        }

        function P() -> value {
            value := P_VALUE
            // value := mload(P_PTR())
        }
        function MASK() -> value {
            value := MASK_VALUE
            // value := mload(MASK_PTR())
        }

        function transcript_4to1_dual(w0, w1) -> r {
            // put to memory 4 coeffs from w0, w1, after SEED (prev hash, FS chain)
            mstore(add(SEED_PTR(), 64), w1)
            mstore(add(SEED_PTR(), 32), w0)
            let seed := keccak256(SEED_PTR(), 96) // hash SEED + 4 coeffs to stack word
            mstore(SEED_PTR(), seed) // immediately dump SEED
            r := shr(128, seed)
        }

        // alpha is the batching challenge needed right after checking outputs
        function transcript128to5_once(ptr) -> z1, z2, z3, z4, alpha {
            calldatacopy(add(SEED_PTR(), 32), ptr, GKR_INIT_BYTES)

            let seed := keccak256(SEED_PTR(), add(32, GKR_INIT_BYTES))
            mstore(SEED_PTR(), seed)
            z1 := shr(128, seed)
            z2 := and(seed, MASK())

            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            z3 := shr(128, seed)
            z4 := and(seed, MASK())

            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            alpha := shr(128, seed)
        }



        // alpha is the batching challenge needed right folding point claims
        function transcript32to3(ptr) -> z1, z2, alpha {
            calldatacopy(add(SEED_PTR(), 32), ptr, GKR_COMPRESSION_POINTCHECK_BYTES)

            let seed := keccak256(SEED_PTR(), add(32, GKR_COMPRESSION_POINTCHECK_BYTES))
            mstore(SEED_PTR(), seed)
            z1 := shr(128, seed)
            z2 := and(seed, MASK())

            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            alpha := shr(128, seed)
        }

        function transcript_init(ptr) -> next_ptr {
            // TODO: we are missing FINAL regs val/ts + FINAL pc/ts
            
            // FIRST: absorb mem caps -> get 7 mem challs
            calldatacopy(add(SEED_PTR(), 32), ptr, MERKLE_TREE_CAPS_BYTES)
            let seed := keccak256(SEED_PTR(), add(32, MERKLE_TREE_CAPS_BYTES))
            mstore(SEED_PTR(), seed)
            mstore(MEMORY_CHALLS_PTR(), shr(128, seed))
            mstore(add(MEMORY_CHALLS_PTR(), 32), and(seed, MASK()))

            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            mstore(add(MEMORY_CHALLS_PTR(), 64), shr(128, seed))
            mstore(add(MEMORY_CHALLS_PTR(), 96), and(seed, MASK()))

            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            mstore(add(MEMORY_CHALLS_PTR(), 128), shr(128, seed))
            mstore(add(MEMORY_CHALLS_PTR(), 160), and(seed, MASK()))

            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            mstore(add(MEMORY_CHALLS_PTR(), 192), shr(128, seed))

            // SECOND: absorb wit+setup caps -> get 2 logup challs
            ptr := add(ptr, MERKLE_TREE_CAPS_BYTES)
            calldatacopy(add(SEED_PTR(), 32), ptr, mul(2, MERKLE_TREE_CAPS_BYTES))
            seed := keccak256(SEED_PTR(), add(32, mul(2, MERKLE_TREE_CAPS_BYTES)))
            mstore(SEED_PTR(), seed)
            mstore(LOGUP_CHALLS_PTR(), shr(128, seed))
            mstore(add(LOGUP_CHALLS_PTR(), 32), and(seed, MASK()))

            next_ptr := add(ptr, mul(2, MERKLE_TREE_CAPS_BYTES))
        }

        function acceval_inlinefold_streamrevlooploop_evenodd(ptr, z1, z2, z3, z4, alpha) -> claim {
            // TODO: inject final values (regs, pc)
            // NB: some stack values are explicitly spilled (fold0 and claim updates):
            //     - when written to, it is after stored
            //     - when read, it is first loaded
            // Same current READ+WRITE work as the open-coded even/odd path, but
            // factored into four quarter chunks under a loop.

            mstore(GKR_INIT_CLAIM_PTR(), claim)
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
                    let num1 := and(MASK(), numword0)
                    let denword0 := calldataload(denbase)
                    let den0 := shr(128, denword0)
                    let den1 := and(MASK(), denword0)
                    num_acc := add(mulmod(num_acc, den0, P()), mulmod(den_acc, num0, P()))
                    den_acc := mulmod(den_acc, den0, P())
                    num_acc := add(mulmod(num_acc, den1, P()), mulmod(den_acc, num1, P()))
                    den_acc := mulmod(den_acc, den1, P())
                    let numfolda := add(num0, mulmod(z4, sub(add(num1, mul(2, P())), num0), P()))
                    let denfolda := add(den0, mulmod(z4, sub(add(den1, mul(2, P())), den0), P()))

                    // fold i+2/3
                    let numword1 := calldataload(add(numbase, 32))
                    let num2 := shr(128, numword1)
                    let num3 := and(MASK(), numword1)
                    let denword1 := calldataload(add(denbase, 32))
                    let den2 := shr(128, denword1)
                    let den3 := and(MASK(), denword1)
                    num_acc := add(mulmod(num_acc, den2, P()), mulmod(den_acc, num2, P()))
                    den_acc := mulmod(den_acc, den2, P())
                    num_acc := add(mulmod(num_acc, den3, P()), mulmod(den_acc, num3, P()))
                    den_acc := mulmod(den_acc, den3, P())
                    let numfoldb := add(num2, mulmod(z4, sub(add(num3, mul(2, P())), num2), P()))
                    let denfoldb := add(den2, mulmod(z4, sub(add(den3, mul(2, P())), den2), P()))

                    // fold i+0/1/2/3
                    let numfoldc := add(numfolda, mulmod(z3, sub(add(numfoldb, mul(3, P())), numfolda), P()))
                    let denfoldc := add(denfolda, mulmod(z3, sub(add(denfoldb, mul(3, P())), denfolda), P()))
                    switch i
                    case 0 {
                        numfold0 := numfoldc
                        mstore(GKR_INIT_SCRATCH_PTR(), numfold0)
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
                if mod(num_acc, P()) { revert(0, 0) }
                if iszero(den_acc) { revert(0, 0) }
                // fold 0/1/2/3/4/5/6/7
                numfold0 := mload(GKR_INIT_SCRATCH_PTR())
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P())), numfold0), P()))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P())), denfold0), P()))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P())), numfold2), P()))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P())), denfold2), P()))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                let num_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P())), numfold0), P()))
                let den_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P())), denfold0), P()))
                // batch
                claim := mload(GKR_INIT_CLAIM_PTR())
                claim := add(mulmod(claim, alpha, P()), den_claim)
                claim := add(mulmod(claim, alpha, P()), num_claim)
                mstore(GKR_INIT_CLAIM_PTR(), claim)
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
                    let prod1 := and(MASK(), word0)
                    prod_acc := mulmod(prod_acc, prod0, P())
                    prod_acc := mulmod(prod_acc, prod1, P())
                    let folda := add(prod0, mulmod(z4, sub(add(prod1, mul(2, P())), prod0), P()))
                    // fold i+2/3
                    let word1 := calldataload(add(base, 32))
                    let prod2 := shr(128, word1)
                    let prod3 := and(MASK(), word1)
                    prod_acc := mulmod(prod_acc, prod2, P())
                    prod_acc := mulmod(prod_acc, prod3, P())
                    let foldb := add(prod2, mulmod(z4, sub(add(prod3, mul(2, P())), prod2), P()))
                    // fold i+0/1/2/3
                    let foldc := add(folda, mulmod(z3, sub(add(foldb, mul(3, P())), folda), P()))
                    switch i
                    case 0 {
                        fold0 := foldc
                        mstore(GKR_INIT_SCRATCH_PTR(), fold0)
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
                fold0 := mload(GKR_INIT_SCRATCH_PTR())
                fold0 := add(fold0, mulmod(z2, sub(add(fold1, mul(4, P())), fold0), P()))
                // fold 8/9/10/11/12/13/14/15
                fold1 := add(fold2, mulmod(z2, sub(add(fold3, mul(4, P())), fold2), P()))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                let prod_claim := add(fold0, mulmod(z1, sub(add(fold1, mul(5, P())), fold0), P()))
                // batch
                claim := mload(GKR_INIT_CLAIM_PTR())
                claim := add(mulmod(claim, alpha, P()), prod_claim)
                mstore(GKR_INIT_CLAIM_PTR(), claim)
            }
            claim := mload(GKR_INIT_CLAIM_PTR())
        }

        function acceval_inlinefold_streamrevlooploop_evenodd_newunchecked(ptr, z1, z2, z3, z4, alpha) -> claim {
            // TODO: inject final values (regs, pc)
            // TODO: this was made by AI, needs to be reviewed
            // NB: some stack values are explicitly spilled (fold0 and claim updates):
            //     - when written to, it is after stored
            //     - when read, it is first loaded
            // Same current READ+WRITE work as the open-coded even/odd path, but
            // factored into four quarter chunks under a loop.

            for { let poly := 6 } gt(poly, 0) { poly := sub(poly, 2) } {
                {
                    let num_acc
                    let den_acc := 1
                    for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                        let numbase := add(add(ptr, mul(poly, GKR_INIT_POLY_BYTES)), mul(i, 64))
                        let denbase := add(add(ptr, mul(add(poly, 1), GKR_INIT_POLY_BYTES)), mul(i, 64))
                        let numword0 := calldataload(numbase)
                        let num0 := shr(128, numword0)
                        let num1 := and(MASK(), numword0)
                        let denword0 := calldataload(denbase)
                        let den0 := shr(128, denword0)
                        let den1 := and(MASK(), denword0)
                        num_acc := add(mulmod(num_acc, den0, P()), mulmod(den_acc, num0, P()))
                        den_acc := mulmod(den_acc, den0, P())
                        num_acc := add(mulmod(num_acc, den1, P()), mulmod(den_acc, num1, P()))
                        den_acc := mulmod(den_acc, den1, P())
                        let numword1 := calldataload(add(numbase, 32))
                        let num2 := shr(128, numword1)
                        let num3 := and(MASK(), numword1)
                        let denword1 := calldataload(add(denbase, 32))
                        let den2 := shr(128, denword1)
                        let den3 := and(MASK(), denword1)
                        num_acc := add(mulmod(num_acc, den2, P()), mulmod(den_acc, num2, P()))
                        den_acc := mulmod(den_acc, den2, P())
                        num_acc := add(mulmod(num_acc, den3, P()), mulmod(den_acc, num3, P()))
                        den_acc := mulmod(den_acc, den3, P())
                    }
                    if mod(num_acc, P()) { revert(0, 0) }
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
                        let num1 := and(MASK(), numword0)
                        let denword0 := calldataload(denbase)
                        let den0 := shr(128, denword0)
                        let den1 := and(MASK(), denword0)
                        let numfolda := add(num0, mulmod(z4, sub(add(num1, mul(2, P())), num0), P()))
                        let denfolda := add(den0, mulmod(z4, sub(add(den1, mul(2, P())), den0), P()))
                        let numword1 := calldataload(add(numbase, 32))
                        let num2 := shr(128, numword1)
                        let num3 := and(MASK(), numword1)
                        let denword1 := calldataload(add(denbase, 32))
                        let den2 := shr(128, denword1)
                        let den3 := and(MASK(), denword1)
                        let numfoldb := add(num2, mulmod(z4, sub(add(num3, mul(2, P())), num2), P()))
                        let denfoldb := add(den2, mulmod(z4, sub(add(den3, mul(2, P())), den2), P()))
                        let numfoldc := add(numfolda, mulmod(z3, sub(add(numfoldb, mul(3, P())), numfolda), P()))
                        let denfoldc := add(denfolda, mulmod(z3, sub(add(denfoldb, mul(3, P())), denfolda), P()))
                        switch i
                        case 0 { numfold0 := numfoldc mstore(GKR_INIT_SCRATCH_PTR(), numfold0) denfold0 := denfoldc }
                        case 1 { numfold1 := numfoldc denfold1 := denfoldc }
                        case 2 { numfold2 := numfoldc denfold2 := denfoldc }
                        default { numfold3 := numfoldc denfold3 := denfoldc }
                    }
                    numfold0 := mload(GKR_INIT_SCRATCH_PTR())
                    numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P())), numfold0), P()))
                    denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P())), denfold0), P()))
                    numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P())), numfold2), P()))
                    denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P())), denfold2), P()))
                    let num_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P())), numfold0), P()))
                    let den_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P())), denfold0), P()))
                    let term_ptr := add(GKR_INIT_CLAIM_PTR(), mul(sub(6, poly), 32))
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
                        prod_acc := mulmod(prod_acc, shr(128, word0), P())
                        prod_acc := mulmod(prod_acc, and(MASK(), word0), P())
                        let word1 := calldataload(add(base, 32))
                        prod_acc := mulmod(prod_acc, shr(128, word1), P())
                        prod_acc := mulmod(prod_acc, and(MASK(), word1), P())
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
                        let prod1 := and(MASK(), word0)
                        let folda := add(prod0, mulmod(z4, sub(add(prod1, mul(2, P())), prod0), P()))
                        let word1 := calldataload(add(base, 32))
                        let prod2 := shr(128, word1)
                        let prod3 := and(MASK(), word1)
                        let foldb := add(prod2, mulmod(z4, sub(add(prod3, mul(2, P())), prod2), P()))
                        let foldc := add(folda, mulmod(z3, sub(add(foldb, mul(3, P())), folda), P()))
                        switch i
                        case 0 { fold0 := foldc mstore(GKR_INIT_SCRATCH_PTR(), fold0) }
                        case 1 { fold1 := foldc }
                        case 2 { fold2 := foldc }
                        default { fold3 := foldc }
                    }
                    fold0 := mload(GKR_INIT_SCRATCH_PTR())
                    fold0 := add(fold0, mulmod(z2, sub(add(fold1, mul(4, P())), fold0), P()))
                    fold1 := add(fold2, mulmod(z2, sub(add(fold3, mul(4, P())), fold2), P()))
                    let prod_claim := add(fold0, mulmod(z1, sub(add(fold1, mul(5, P())), fold0), P()))
                    mstore(add(GKR_INIT_CLAIM_PTR(), sub(224, mul(poly, 32))), prod_claim)
                }
            }
            claim := 0
            for { let off := 0 } lt(off, 256) { off := add(off, 32) } {
                claim := add(mulmod(claim, alpha, P()), mload(add(GKR_INIT_CLAIM_PTR(), off)))
            }
        }

        // Strategy 2: absorb the init block and draw z1..z4 and alpha, but do not
        // store full eq[16]. Instead, generate eq factors inline while streaming
        // over calldata so folding and accumulator updates happen in one pass.
        function gkr_init_inlinefold(ptr) -> next_ptr, claim, alpha {
            let z1, z2, z3, z4
            z1, z2, z3, z4, alpha := transcript128to5_once(ptr)
            mstore(POINT_PTR(), z1)
            mstore(add(POINT_PTR(), 32), z2)
            mstore(add(POINT_PTR(), 64), z3)
            mstore(add(POINT_PTR(), 96), z4)

            // claim := acceval_inlinefold_streamrevlooploop_evenodd(ptr, z1, z2, z3, z4, alpha)
            claim := acceval_inlinefold_streamrevlooploop_evenodd_newunchecked(ptr, z1, z2, z3, z4, alpha)

            next_ptr := add(ptr, GKR_INIT_BYTES)
        }

        function sumcheck_rounds(ptr, claim, total_rounds) -> next_ptr, next_claim, eq_scale {
            eq_scale := 1
            for { let i := 0 } lt(i, total_rounds) { i := add(i, 1) } {
                let w0 := calldataload(ptr)
                let w1 := calldataload(add(ptr, 32))
                let c0 := shr(128, w0)
                let c1 := and(w0, MASK())
                let c2 := shr(128, w1)
                let c3 := and(w1, MASK())
                let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P())
                let r := transcript_4to1_dual(w0, w1) // before-check draw is intentional; see HEURISTICS.md
                // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
                if mod(add(claim, sub(P(), g0g1_scaled)), P()) { revert(0, 0) }
                claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P()), c2), r, P()), c1), r, P()), c0)
                let z := mload(add(POINT_PTR(), mul(i, 32)))
                let zr := mulmod(z, r, P())
                eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P()), add(z, r)))
                mstore(add(POINT_PTR(), mul(i, 32)), r)
                ptr := add(ptr, 64)
            }
            next_ptr := ptr
            next_claim := claim
        }

        function sumcheck_compress_2pass(ptr, claim, alpha, rounds_skiplast) -> next_ptr, next_claim, next_alpha {
            // START WITH LAYER: 2^4 poly -> 2^5 polys (last var skip)
            // let rounds_skiplast := 3 // keep this const for now
            // TODO: can offload alpha to memory bc it's used only in the end
            let eq_scale
            ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, rounds_skiplast)

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
                let den1 := and(MASK(), denword)
                let den_acc := mulmod(den0, den1, P())
                acc0 := add(mulmod(acc0, alpha, P()), den_acc)

                let numword := calldataload(numbase)
                let num0 := shr(128, numword)
                let num1 := and(MASK(), numword)
                let num_acc := add(mulmod(num0, den1, P()), mulmod(num1, den0, P()))
                acc0 := add(mulmod(acc0, alpha, P()), num_acc)
            }
            for { let poly := 1 } lt(poly, 2) { poly := sub(poly, 1) } {
                let base := add(ptr, mul(poly, GKR_COMPRESSION_POINTCHECK_POLY_BYTES))
                let word := calldataload(base)
                let prod0 := shr(128, word)
                let prod1 := and(MASK(), word)
                let contribution := mulmod(prod0, prod1, P())
                acc0 := add(mulmod(acc0, alpha, P()), contribution)
            }
            let acc1 // compute RLC for x4 == 1
            for { let poly := 6 } gt(poly, 0) { poly := sub(poly, 2) } {
                // TODO: collect den0 and combine den_acc*alpha + num_acc as
                // d0 * (d1 * alpha + n1) + n0 * d1; revisit other logup paths too.
                let numbase := add(ptr, mul(poly, GKR_COMPRESSION_POINTCHECK_POLY_BYTES))
                let denbase := add(ptr, mul(add(poly, 1), GKR_COMPRESSION_POINTCHECK_POLY_BYTES))
                let denword := calldataload(add(denbase, 32))

                let den0 := shr(128, denword)
                let den1 := and(MASK(), denword)
                let den_acc := mulmod(den0, den1, P())
                acc1 := add(mulmod(acc1, alpha, P()), den_acc)

                let numword := calldataload(add(numbase, 32))
                let num0 := shr(128, numword)
                let num1 := and(MASK(), numword)
                let num_acc := add(mulmod(num0, den1, P()), mulmod(num1, den0, P()))
                acc1 := add(mulmod(acc1, alpha, P()), num_acc)
            }
            for { let poly := 1 } lt(poly, 2) { poly := sub(poly, 1) } {
                let base := add(ptr, mul(poly, GKR_COMPRESSION_POINTCHECK_POLY_BYTES))
                let word := calldataload(add(base, 32))
                let prod0 := shr(128, word)
                let prod1 := and(MASK(), word)
                let contribution := mulmod(prod0, prod1, P())
                acc1 := add(mulmod(acc1, alpha, P()), contribution)
            }
            let diff := add(acc1, sub(mul(2, P()), acc0))
            let z_last := mload(add(POINT_PTR(), mul(rounds_skiplast, 32)))
            let rhs_scaled := mulmod(add(acc0, mulmod(z_last, diff, P())), eq_scale, P())
            // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
            if mod(add(claim, sub(P(), rhs_scaled)), P()) { revert(0, 0) }

            // POINT CLAIMS INTERPOLATE + BATCH
            // TODO: if compilation is good, try to merge this with POINTCHECK
            // remember to reset ptr back..
            let r_last, r_pair // ie. new (zN, zN+1) points
            r_last, r_pair, next_alpha := transcript32to3(ptr)
            mstore(add(POINT_PTR(), mul(rounds_skiplast, 32)), r_last)
            mstore(add(POINT_PTR(), mul(add(rounds_skiplast, 1), 32)), r_pair)
            for { let poly := 7 } lt(poly, 8) { poly := sub(poly, 1) } {
                let base := add(ptr, mul(poly, GKR_COMPRESSION_POINTCHECK_POLY_BYTES))

                let word0 := calldataload(base)
                let el0 := shr(128, word0)
                let el1 := and(MASK(), word0)
                let claim0 := add(el0, mulmod(r_pair, add(el1, sub(mul(2, P()), el0)), P()))

                let word1 := calldataload(add(base, 32))
                let el2 := shr(128, word1)
                let el3 := and(MASK(), word1)
                let claim1 := add(el2, mulmod(r_pair, add(el3, sub(mul(2, P()), el2)), P()))

                let poly_claim := add(claim0, mulmod(r_last, add(claim1, sub(mul(3, P()), claim0)), P()))
                next_claim := add(mulmod(next_claim, next_alpha, P()), poly_claim)
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

        // SPILL OVERWRITE PREVENTION
        if gt(mload(0x40), MINIMUM_FREE_HEAP_PTR) {
            revert(0, 0)
        }
        // prepare constants
        mstore(P_PTR(), P_VALUE)
        mstore(MASK_PTR(), MASK_VALUE)

        // INIT MAIN
        // Stash starting gas to memory across the gkr_init_* call so that
        // Yul stack spills can't corrupt it under high register pressure.
        let ptr, claim, alpha
        {
            mstore(GKR_INIT_GAS_PTR(), gas())
            mstore(SEED_PTR(), 0) // SEED Transcript, FINE as long as we don't draw without absorb!
            ptr := transcript_init(0)
            ptr, claim, alpha := gkr_init_inlinefold(ptr)
            let init_gas := sub(mload(GKR_INIT_GAS_PTR()), gas())
            mstore(GKR_INIT_GAS_PTR(), init_gas)
        }

        // MAIN
        {
            mstore(GKR_MAIN_GAS_PTR(), gas())
            ptr, claim, alpha := gkr_compress(ptr, claim, alpha)
            ptr, claim, alpha := gkr_circuit(ptr, claim, alpha)
            let compress_gas := sub(mload(GKR_MAIN_GAS_PTR()), gas())
            mstore(GKR_MAIN_GAS_PTR(), compress_gas)
        }

        // DONE: Proof empty now
        // for { let i := 0 } lt(i, 10) { i := add(i, 1) } {
        //     if calldataload(add(ptr, mul(i, 32))) { revert(0, 0) }
        // }

        // TODO: don't forget the recursion chain check
        // TODO: very, VERY, carefully review end-to-end fiat-shamir

        // anti-DCE
        mstore(0, claim)
        mstore(32, mload(GKR_INIT_GAS_PTR()))
        mstore(64, mload(GKR_MAIN_GAS_PTR()))
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
    returns (bytes memory capsData, bytes32 state, uint256 logupAlpha, uint256 logupGamma, uint256[7] memory mc)
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

    // Mirror transcript_init: absorb mem caps, then draw 7 memory challenges
    // over four keccak rounds (mc[0..5] are the 6 tuple-compression challs,
    // mc[6] the additive one), then absorb wit+setup caps for the 2 logup challs.
    state = keccak256(abi.encodePacked(bytes32(0), memCaps));
    mc[0] = uint256(state) >> 128;
    mc[1] = uint128(uint256(state));
    state = keccak256(abi.encodePacked(state));
    mc[2] = uint256(state) >> 128;
    mc[3] = uint128(uint256(state));
    state = keccak256(abi.encodePacked(state));
    mc[4] = uint256(state) >> 128;
    mc[5] = uint128(uint256(state));
    state = keccak256(abi.encodePacked(state));
    mc[6] = uint256(state) >> 128;
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
    (bytes memory capsData, bytes32 state, uint256 logupAlpha, uint256 logupGamma, uint256[7] memory memChalls) =
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

    out = generate_after_init(out, state, claim, alpha, zpoint, coeff_seed, logupAlpha, logupGamma, memChalls);
}

function generate_after_init(
    bytes memory out,
    bytes32 state,
    uint256 claim,
    uint256 alpha,
    uint256[24] memory zpoint,
    bytes32 coeff_seed,
    uint256 logupAlpha,
    uint256 logupGamma,
    uint256[7] memory memChalls
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
    (out, state, claim, alpha) = generate_circuit_layer0(
        out, state, claim, alpha, zpoint, keccak256(abi.encodePacked(coeff_seed, "circuit-layer-0")),
        logupAlpha, logupGamma, memChalls
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

// ===========================================================================
// === Layer-0 mock calldata generator (mirrors sumcheck_circuit_layer0) =====
// ===========================================================================
// Layer 0 is the base layer: its point check folds 155 gate evaluations
// (Horner in alpha) over 113 base-column point values and asserts
// acc*eq_scale == claim. The acc body below is AUTO-TRANSLATED from
// circuit.yul operation-for-operation (add->+, sub->-, mul->*, mulmod->mulmod)
// inside `unchecked`, so it bit-matches the verifier's EVM arithmetic (every
// intermediate is provably < 2^152, so there is no 2^256 wrap). The patch then
// solves a single linearly-appearing point so the real check passes.

function l0_memrel(uint256 addr_space, uint256 addr_low, uint256 addr_high, uint256 ts_low, uint256 ts_high, uint256 val_low, uint256 val_high, uint256[7] memory mc, uint256 p) pure returns (uint256 c) {
    unchecked {
        c = mc[6] + addr_space;
        c = c + mulmod(mc[0], addr_low, p);
        c = c + mulmod(mc[1], addr_high, p);
        c = c + mulmod(mc[2], ts_low, p);
        c = c + mulmod(mc[3], ts_high, p);
        c = c + mulmod(mc[4], val_low, p);
        c = c + mulmod(mc[5], val_high, p);
    }
}

function l0_memrelHigh(uint256 ts_low, uint256 ts_high, uint256 val_low, uint256 val_high, uint256[7] memory mc, uint256 p) pure returns (uint256 c) {
    unchecked {
        c = mulmod(mc[2], ts_low, p);
        c = c + mulmod(mc[3], ts_high, p);
        c = c + mulmod(mc[4], val_low, p);
        c = c + mulmod(mc[5], val_high, p);
    }
}

function l0_lookrelHalf(uint256 acc, uint256 c0, uint256 c1, uint256 c2, uint256 c3, uint256 c4, uint256 beta, uint256 p) pure returns (uint256 r) {
    unchecked {
        r = mulmod(acc, beta, p) + c4;
        r = mulmod(r, beta, p) + c3;
        r = mulmod(r, beta, p) + c2;
        r = mulmod(r, beta, p) + c1;
        r = mulmod(r, beta, p) + c0;
    }
}

function l0_composeVars(uint256 len, uint256 skip, uint256[24] memory point) pure returns (uint256 eval) {
    unchecked {
        uint256 max = 24 - skip; // GKR_CIRCUIT_LAYER_ROUNDS
        uint256 min = max - len;
        for (uint256 i = min; i < max; ++i) {
            eval = eval * 2 + point[i];
        }
    }
}

function l0_zeroVars(uint256 len, uint256[24] memory point) pure returns (uint256 eval) {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    unchecked {
        eval = 1;
        for (uint256 i = 0; i < len; ++i) {
            eval = mulmod(eval, 1 + 2 * p - point[i], p);
        }
    }
}

function l0_rangecheck(uint256 width, uint256[24] memory point, uint256 p) pure returns (uint256) {
    return mulmod(l0_composeVars(width, 0, point), l0_zeroVars(24 - width, point), p);
}

// Wrappers so the auto-translated body can call the bare names it was emitted with.
function memrel(uint256 a0, uint256 a1, uint256 a2, uint256 a3, uint256 a4, uint256 a5, uint256 a6, uint256[7] memory mc, uint256 p) pure returns (uint256) { return l0_memrel(a0,a1,a2,a3,a4,a5,a6,mc,p); }
function memrelHigh(uint256 a0, uint256 a1, uint256 a2, uint256 a3, uint256[7] memory mc, uint256 p) pure returns (uint256) { return l0_memrelHigh(a0,a1,a2,a3,mc,p); }
function lookrelHalf(uint256 a, uint256 c0, uint256 c1, uint256 c2, uint256 c3, uint256 c4, uint256 beta, uint256 p) pure returns (uint256) { return l0_lookrelHalf(a,c0,c1,c2,c3,c4,beta,p); }
function composeVars(uint256 len, uint256 skip, uint256[24] memory point) pure returns (uint256) { return l0_composeVars(len,skip,point); }
function rangecheck(uint256 width, uint256[24] memory point, uint256 p) pure returns (uint256) { return l0_rangecheck(width,point,p); }

function circuit_layer0_acc(
    uint256[] memory v,
    uint256 alpha,
    uint256[7] memory mc,
    uint256 beta,
    uint256 delta,
    uint256[24] memory point
) pure returns (uint256 acc) {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    uint256[4] memory cache;
    unchecked {
    {
        uint256 gate = rangecheck(16, point, p);
        cache[0] = gate % p;
    }
    {
        uint256 gate = rangecheck(19, point, p);
        cache[1] = gate % p;
    }
    {
        uint256 gate = (4 * composeVars(14, 0, point));
        cache[2] = gate % p;
    }
    {
        uint256 gate = composeVars(10, 14, point);
        cache[3] = gate % p;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[99]))) + mulmod(v[99], (1 * v[99]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[98]))) + mulmod(v[98], (1 * v[98]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[97]))) + mulmod(v[97], (1 * v[97]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[96]))) + mulmod(v[96], (1 * v[96]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[95]))) + mulmod(v[95], (1 * v[95]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[94]))) + mulmod(v[94], (1 * v[94]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[93]))) + mulmod(v[93], (1 * v[93]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[92]))) + mulmod(v[92], (1 * v[92]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[91]))) + mulmod(v[91], (1 * v[91]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[90]))) + mulmod(v[90], (1 * v[90]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[63]))) + mulmod(v[63], (1 * v[63]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[62]))) + mulmod(v[62], (1 * v[62]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[61]))) + mulmod(v[61], (1 * v[61]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[60]))) + mulmod(v[60], (1 * v[60]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[59]))) + mulmod(v[59], (1 * v[59]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[16]))) + mulmod(v[16], (1 * v[16]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[9]))) + mulmod(v[9], (1 * v[9]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[58]))) + mulmod(v[58], (1 * v[58]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[57]))) + mulmod(v[57], (1 * v[57]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[56]))) + mulmod(v[56], (1 * v[56]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[55]))) + mulmod(v[55], (1 * v[55]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[54]))) + mulmod(v[54], (1 * v[54]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[53]))) + mulmod(v[53], (1 * v[53]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[52]))) + mulmod(v[52], (1 * v[52]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[51]))) + mulmod(v[51], (1 * v[51]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[50]))) + mulmod(v[50], (1 * v[50]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[49]))) + mulmod(v[49], (1 * v[49]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[48]))) + mulmod(v[48], (1 * v[48]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[47]))) + mulmod(v[47], (1 * v[47]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[46]))) + mulmod(v[46], (1 * v[46]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[45]))) + mulmod(v[45], (1 * v[45]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[44]))) + mulmod(v[44], (1 * v[44]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[43]))) + mulmod(v[43], (1 * v[43]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((15360 + ((((3840 * v[24]) + (1 * ((2 * p) - v[25]))) + (3840 * ((2 * p) - v[28]))) + (1 * v[29]))) + 0);
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((235944960 + ((117968640 * v[24]) + (117968640 * ((2 * p) - v[28])))) + (mulmod(v[24], ((14745600 * v[24]) + (29491200 * ((2 * p) - v[28]))), p) + mulmod(v[28], (14745600 * v[28]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + ((((((((((((((((((1 * v[43]) + (1 * v[44])) + (1 * v[45])) + (1 * v[46])) + (1 * v[47])) + (1 * v[48])) + (1 * v[49])) + (1 * v[50])) + (1 * v[51])) + (1 * v[52])) + (1 * v[53])) + (1 * v[54])) + (1 * v[55])) + (1 * v[56])) + (1 * v[57])) + (1 * v[58])) + (1 * v[9])) + (1 * v[16]))) + (((((((((((((((((mulmod(v[43], (1 * ((2 * p) - v[21])), p) + mulmod(v[44], (1 * ((2 * p) - v[21])), p)) + mulmod(v[45], (1 * ((2 * p) - v[21])), p)) + mulmod(v[46], (1 * ((2 * p) - v[21])), p)) + mulmod(v[47], (1 * ((2 * p) - v[21])), p)) + mulmod(v[48], (1 * ((2 * p) - v[21])), p)) + mulmod(v[49], (1 * ((2 * p) - v[21])), p)) + mulmod(v[50], (1 * ((2 * p) - v[21])), p)) + mulmod(v[51], (1 * ((2 * p) - v[21])), p)) + mulmod(v[52], (1 * ((2 * p) - v[21])), p)) + mulmod(v[53], (1 * ((2 * p) - v[21])), p)) + mulmod(v[54], (1 * ((2 * p) - v[21])), p)) + mulmod(v[55], (1 * ((2 * p) - v[21])), p)) + mulmod(v[56], (1 * ((2 * p) - v[21])), p)) + mulmod(v[57], (1 * ((2 * p) - v[21])), p)) + mulmod(v[58], (1 * ((2 * p) - v[21])), p)) + mulmod(v[9], (1 * ((2 * p) - v[21])), p)) + mulmod(v[16], (1 * ((2 * p) - v[21])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * v[96])) + ((((((((((((((((mulmod(v[43], (1 * ((2 * p) - v[21])), p) + mulmod(v[44], (1 * ((2 * p) - v[21])), p)) + mulmod(v[45], (1 * ((2 * p) - v[21])), p)) + mulmod(v[46], (1 * ((2 * p) - v[21])), p)) + mulmod(v[47], (1 * ((2 * p) - v[21])), p)) + mulmod(v[48], (1 * ((2 * p) - v[21])), p)) + mulmod(v[49], (1 * ((2 * p) - v[21])), p)) + mulmod(v[50], (1 * ((2 * p) - v[21])), p)) + mulmod(v[51], (1 * ((2 * p) - v[21])), p)) + mulmod(v[52], (1 * ((2 * p) - v[21])), p)) + mulmod(v[53], (1 * ((2 * p) - v[21])), p)) + mulmod(v[54], (1 * ((2 * p) - v[21])), p)) + mulmod(v[55], (1 * ((2 * p) - v[21])), p)) + mulmod(v[57], (1 * ((2 * p) - v[21])), p)) + mulmod(v[58], (1 * ((2 * p) - v[21])), p)) + mulmod(v[9], (1 * ((2 * p) - v[21])), p)) + mulmod(v[16], (1 * ((2 * p) - v[21])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (mulmod(v[94], (1 * v[95]), p) + mulmod(v[95], ((1 * v[23]) + (1 * ((2 * p) - v[27]))), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (4 * v[95])) + (mulmod(v[94], (65536 * ((2 * p) - v[95])), p) + mulmod(v[95], ((1 * v[22]) + (1 * ((2 * p) - v[26]))), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + ((1 * v[95]) + (1 * ((2 * p) - v[21])))) + (((mulmod(v[52], (1 * v[21]), p) + mulmod(v[53], (1 * v[21]), p)) + mulmod(v[54], (1 * v[21]), p)) + mulmod(v[55], (1 * v[21]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (mulmod(v[62], (1 * v[16]), p) + mulmod(v[63], (1 * v[16]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (((mulmod(v[62], (1 * v[16]), p) + mulmod(v[63], (2 * v[16]), p)) + mulmod(v[85], (4 * v[16]), p)) + mulmod(v[16], (1 * ((2 * p) - v[17])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * v[93])) + mulmod(v[61], ((1 * ((2 * p) - v[9])) + (1 * ((2 * p) - v[16]))), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[61], (1 * v[16]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (mulmod(v[65], (1 * v[16]), p) + mulmod(v[16], (1 * ((2 * p) - v[18])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (mulmod(v[65], (1 * v[9]), p) + mulmod(v[9], (1 * ((2 * p) - v[11])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (mulmod(v[64], (1 * v[16]), p) + mulmod(v[16], (1 * ((2 * p) - v[17])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (mulmod(v[64], (1 * v[9]), p) + mulmod(v[9], (1 * ((2 * p) - v[10])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (((((mulmod(v[41], ((1 * v[9]) + (1 * v[16])), p) + mulmod(v[59], ((1 * v[9]) + (1 * v[16])), p)) + mulmod(v[60], ((65536 * ((2 * p) - v[9])) + (65536 * ((2 * p) - v[16]))), p)) + mulmod(v[3], ((1 * v[9]) + (1 * v[16])), p)) + mulmod(v[9], (1 * ((2 * p) - v[11])), p)) + mulmod(v[16], (1 * ((2 * p) - v[18])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + ((((mulmod(v[40], ((1 * v[9]) + (1 * v[16])), p) + mulmod(v[59], ((65536 * ((2 * p) - v[9])) + (65536 * ((2 * p) - v[16]))), p)) + mulmod(v[2], ((1 * v[9]) + (1 * v[16])), p)) + mulmod(v[9], (1 * ((2 * p) - v[10])), p)) + mulmod(v[16], (1 * ((2 * p) - v[17])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * v[18])) + mulmod(v[16], (1 * ((2 * p) - v[18])), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + ((1 * ((2 * p) - v[39])) + (1 * v[17]))) + (mulmod(v[39], (1 * v[16]), p) + mulmod(v[16], (1 * ((2 * p) - v[17])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * v[11])) + mulmod(v[9], (1 * ((2 * p) - v[11])), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + ((1 * ((2 * p) - v[38])) + (1 * v[10]))) + (mulmod(v[38], (1 * v[9]), p) + mulmod(v[9], (1 * ((2 * p) - v[10])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (mulmod(v[57], (((((((((1 * v[67]) + (256 * v[68])) + (1 * v[71])) + (256 * v[72])) + (1 * v[75])) + (256 * v[76])) + (1 * v[79])) + (256 * v[80])) + (1 * ((2 * p) - v[20]))), p) + mulmod(v[58], (((1 * v[67]) + (256 * v[68])) + (1 * ((2 * p) - v[20]))), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (mulmod(v[57], (((((((((1 * v[65]) + (256 * v[66])) + (1 * v[69])) + (256 * v[70])) + (1 * v[73])) + (256 * v[74])) + (1 * v[77])) + (256 * v[78])) + (1 * ((2 * p) - v[19]))), p) + mulmod(v[58], (((1 * v[65]) + (256 * v[66])) + (1 * ((2 * p) - v[19]))), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + ((1 * ((2 * p) - v[57])) + (1 * ((2 * p) - v[58])))) + (mulmod(v[57], ((1 * v[57]) + (2 * v[58])), p) + mulmod(v[58], (1 * v[58]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[92], (1 * v[20]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[92], (1 * v[19]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[91], (1 * v[20]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (mulmod(v[86], (1 * v[90]), p) + mulmod(v[90], (1 * ((2 * p) - v[20])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (((mulmod(v[66], (1 * v[91]), p) + mulmod(v[85], (1 * v[90]), p)) + mulmod(v[90], (1 * ((2 * p) - v[19])), p)) + mulmod(v[91], (1 * ((2 * p) - v[19])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * v[92])) + (((mulmod(v[52], (1 * ((2 * p) - v[56])), p) + mulmod(v[53], (1 * ((2 * p) - v[56])), p)) + mulmod(v[54], (1 * ((2 * p) - v[56])), p)) + mulmod(v[55], (1 * ((2 * p) - v[56])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + ((1 * ((2 * p) - v[54])) + (1 * v[91]))) + mulmod(v[54], (1 * v[56]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (((1 * ((2 * p) - v[52])) + (1 * ((2 * p) - v[53]))) + (1 * v[90]))) + (mulmod(v[52], (1 * v[56]), p) + mulmod(v[53], (1 * v[56]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + ((mulmod(v[52], (1 * v[63]), p) + mulmod(v[53], (1 * v[63]), p)) + mulmod(v[63], (1 * v[89]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + ((((mulmod(v[41], (((1 * v[52]) + (1 * v[53])) + (1 * v[89])), p) + mulmod(v[52], ((((1 * v[61]) + (65536 * ((2 * p) - v[62]))) + (1 * v[23])) + (1 * ((2 * p) - v[27]))), p)) + mulmod(v[53], ((((1 * v[61]) + (65536 * ((2 * p) - v[62]))) + (1 * v[3])) + (1 * ((2 * p) - v[27]))), p)) + mulmod(v[54], ((((1 * v[61]) + (65536 * ((2 * p) - v[62]))) + (1 * v[23])) + (1 * ((2 * p) - v[27]))), p)) + mulmod(v[55], ((((1 * v[61]) + (65536 * ((2 * p) - v[62]))) + (1 * v[23])) + (1 * ((2 * p) - v[27]))), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (((4 * v[54]) + (4 * v[55])) + (4 * ((2 * p) - v[89])))) + ((((mulmod(v[40], (((1 * v[52]) + (1 * v[53])) + (1 * v[89])), p) + mulmod(v[52], (((65536 * ((2 * p) - v[61])) + (1 * ((2 * p) - v[88]))) + (1 * v[22])), p)) + mulmod(v[53], (((65536 * ((2 * p) - v[61])) + (1 * ((2 * p) - v[88]))) + (1 * v[2])), p)) + mulmod(v[54], (((65536 * ((2 * p) - v[61])) + (1 * ((2 * p) - v[88]))) + (1 * v[22])), p)) + mulmod(v[55], (((65536 * ((2 * p) - v[61])) + (1 * ((2 * p) - v[88]))) + (1 * v[22])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[89]))) + mulmod(v[55], (1 * v[66]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + ((((mulmod(v[41], (1 * v[54]), p) + mulmod(v[52], ((((1 * v[59]) + (65536 * ((2 * p) - v[60]))) + (1 * ((2 * p) - v[86]))) + (1 * v[23])), p)) + mulmod(v[53], ((((1 * v[59]) + (65536 * ((2 * p) - v[60]))) + (1 * ((2 * p) - v[86]))) + (1 * v[23])), p)) + mulmod(v[54], (((((1 * v[59]) + (65536 * ((2 * p) - v[60]))) + (1 * v[86])) + (1 * ((2 * p) - v[3]))) + (1 * v[8])), p)) + mulmod(v[55], (((((1 * v[59]) + (65536 * ((2 * p) - v[60]))) + (1 * v[86])) + (1 * ((2 * p) - v[3]))) + (1 * v[8])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + ((4 * v[52]) + (4 * v[53]))) + ((((mulmod(v[40], (1 * v[54]), p) + mulmod(v[52], (((65536 * ((2 * p) - v[59])) + (1 * ((2 * p) - v[85]))) + (1 * v[22])), p)) + mulmod(v[53], (((65536 * ((2 * p) - v[59])) + (1 * ((2 * p) - v[85]))) + (1 * v[22])), p)) + mulmod(v[54], ((((65536 * ((2 * p) - v[59])) + (1 * v[85])) + (1 * ((2 * p) - v[2]))) + (1 * v[7])), p)) + mulmod(v[55], ((((65536 * ((2 * p) - v[59])) + (1 * v[85])) + (1 * ((2 * p) - v[2]))) + (1 * v[7])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[50], (1 * v[20]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[50], (1 * v[19]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[50], (1 * v[6]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[50], (1 * v[5]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[50], (1 * v[8]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[50], (1 * v[7]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + ((((30720 * v[46]) + (30720 * v[47])) + (30720 * v[48])) + (30720 * v[49]))) + (((((((mulmod(v[41], ((1 * v[43]) + (1 * v[45])), p) + mulmod(v[43], (((((65536 * ((2 * p) - v[59])) + (1 * v[60])) + (1 * v[3])) + (1 * v[8])) + (1 * ((2 * p) - v[20]))), p)) + mulmod(v[44], (((((65536 * ((2 * p) - v[59])) + (1 * v[60])) + (1 * ((2 * p) - v[3]))) + (1 * v[8])) + (1 * v[20])), p)) + mulmod(v[45], ((((65536 * ((2 * p) - v[59])) + (1 * v[60])) + (1 * ((2 * p) - v[20]))) + (1 * v[23])), p)) + mulmod(v[46], ((((65536 * ((2 * p) - v[59])) + (1 * v[60])) + (1 * v[86])) + (1 * ((2 * p) - v[20]))), p)) + mulmod(v[47], ((((65536 * ((2 * p) - v[59])) + (1 * v[60])) + (1 * v[86])) + (1 * ((2 * p) - v[20]))), p)) + mulmod(v[48], ((((65536 * ((2 * p) - v[59])) + (1 * v[60])) + (1 * v[86])) + (1 * ((2 * p) - v[20]))), p)) + mulmod(v[49], ((((65536 * ((2 * p) - v[59])) + (1 * v[60])) + (1 * v[86])) + (1 * ((2 * p) - v[20]))), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + ((((1 * v[46]) + (1 * v[47])) + (1 * v[48])) + (1 * v[49]))) + (((((((mulmod(v[40], ((1 * v[43]) + (1 * v[45])), p) + mulmod(v[43], ((((65536 * ((2 * p) - v[60])) + (1 * v[2])) + (1 * v[7])) + (1 * ((2 * p) - v[19]))), p)) + mulmod(v[44], ((((65536 * ((2 * p) - v[60])) + (1 * ((2 * p) - v[2]))) + (1 * v[7])) + (1 * v[19])), p)) + mulmod(v[45], (((65536 * ((2 * p) - v[60])) + (1 * ((2 * p) - v[19]))) + (1 * v[22])), p)) + mulmod(v[46], (((65536 * ((2 * p) - v[60])) + (1 * v[85])) + (1 * ((2 * p) - v[19]))), p)) + mulmod(v[47], (((65536 * ((2 * p) - v[60])) + (1 * v[85])) + (1 * ((2 * p) - v[19]))), p)) + mulmod(v[48], (((65536 * ((2 * p) - v[60])) + (1 * v[85])) + (1 * ((2 * p) - v[19]))), p)) + mulmod(v[49], (((65536 * ((2 * p) - v[60])) + (1 * v[85])) + (1 * ((2 * p) - v[19]))), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + ((((1 * v[46]) + (1 * v[47])) + (1 * v[48])) + (1 * v[49]))) + (((mulmod(v[46], (1 * ((2 * p) - v[59])), p) + mulmod(v[47], (1 * ((2 * p) - v[59])), p)) + mulmod(v[48], (1 * ((2 * p) - v[59])), p)) + mulmod(v[49], (1 * ((2 * p) - v[59])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (((mulmod(v[46], ((((((1 * ((2 * p) - v[2])) + (65536 * ((2 * p) - v[3]))) + (1 * ((2 * p) - v[7]))) + (65536 * ((2 * p) - v[8]))) + (1 * v[19])) + (65536 * v[20])), p) + mulmod(v[47], ((((((1 * ((2 * p) - v[2])) + (65536 * ((2 * p) - v[3]))) + (1 * v[7])) + (65536 * v[8])) + (1 * v[19])) + (65536 * v[20])), p)) + mulmod(v[48], (((1 * ((2 * p) - v[87])) + (1 * v[19])) + (65536 * v[20])), p)) + mulmod(v[49], (((1 * ((2 * p) - v[87])) + (1 * v[19])) + (65536 * v[20])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[87]))) + ((mulmod(v[49], ((1 * v[14]) + (65536 * v[15])), p) + mulmod(v[2], ((943718400 * v[7]) + (30720 * ((2 * p) - v[8]))), p)) + mulmod(v[3], ((30720 * ((2 * p) - v[7])) + (1 * v[8])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * ((2 * p) - v[21]))) + mulmod(v[21], (1 * v[21]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 input_den = (delta + lookrelHalf(lookrelHalf(0, (0 + (1 * v[40])), (0 + (1 * v[41])), (0 + (1 * v[42])), (0 + ((((((((((((((((((1 * v[43]) + (2 * v[44])) + (4 * v[45])) + (8 * v[46])) + (16 * v[47])) + (32 * v[48])) + (64 * v[49])) + (128 * v[50])) + (256 * v[51])) + (512 * v[52])) + (1024 * v[53])) + (2048 * v[54])) + (4096 * v[55])) + (8192 * v[56])) + (16384 * v[57])) + (32768 * v[58])) + (65536 * v[9])) + (131072 * v[16]))), (46 + 0), beta, p), (0 + (1 * v[22])), (0 + (1 * v[23])), (0 + (1 * v[4])), (0 + (1 * v[38])), (0 + (1 * v[39])), beta, p));
        uint256 setup_den = (delta + lookrelHalf(lookrelHalf(0, v[108], v[109], v[110], v[111], v[112], beta, p), v[103], v[104], v[105], v[106], v[107], beta, p));
        uint256 den_out = mulmod(input_den, setup_den, p);
        uint256 gate = den_out;
        acc = mulmod(acc, alpha, p) + gate;
        uint256 num_out = (mulmod(v[21], setup_den, p) + (p - mulmod(input_den, v[102], p)));
        gate = num_out;
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = (524288 + (((1 * ((2 * p) - v[25])) + (1 * v[13])) + (1 * ((2 * p) - v[99]))));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 den_out = mulmod((delta + (524288 + (((1 * ((2 * p) - v[25])) + (1 * v[6])) + (1 * ((2 * p) - v[98]))))), (delta + ((p - 2) + (((1 * ((2 * p) - v[24])) + (1 * v[12])) + (524288 * v[99])))), p);
        uint256 gate = den_out;
        acc = mulmod(acc, alpha, p) + gate;
        uint256 num_out = ((delta + (524288 + (((1 * ((2 * p) - v[25])) + (1 * v[6])) + (1 * ((2 * p) - v[98]))))) + (delta + ((p - 2) + (((1 * ((2 * p) - v[24])) + (1 * v[12])) + (524288 * v[99])))));
        gate = num_out;
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 den_out = mulmod((delta + (524288 + (((1 * ((2 * p) - v[25])) + (1 * v[1])) + (1 * ((2 * p) - v[97]))))), (delta + ((p - 1) + (((1 * ((2 * p) - v[24])) + (1 * v[5])) + (524288 * v[98])))), p);
        uint256 gate = den_out;
        acc = mulmod(acc, alpha, p) + gate;
        uint256 num_out = ((delta + (524288 + (((1 * ((2 * p) - v[25])) + (1 * v[1])) + (1 * ((2 * p) - v[97]))))) + (delta + ((p - 1) + (((1 * ((2 * p) - v[24])) + (1 * v[5])) + (524288 * v[98])))));
        gate = num_out;
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 den_out = mulmod((delta + (0 + (1 * v[29]))), (delta + (0 + (((1 * ((2 * p) - v[24])) + (1 * v[0])) + (524288 * v[97])))), p);
        uint256 gate = den_out;
        acc = mulmod(acc, alpha, p) + gate;
        uint256 num_out = ((delta + (0 + (1 * v[29]))) + (delta + (0 + (((1 * ((2 * p) - v[24])) + (1 * v[0])) + (524288 * v[97])))));
        gate = num_out;
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 den_out = mulmod((delta + v[28]), (delta + cache[1]), p);
        uint256 gate = den_out;
        acc = mulmod(acc, alpha, p) + gate;
        uint256 num_out = ((delta + cache[1]) + (p - mulmod(v[101], (delta + v[28]), p)));
        gate = num_out;
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = v[27];
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 den_out = mulmod((delta + (0 + (1 * v[18]))), (delta + (0 + (1 * v[26]))), p);
        uint256 gate = den_out;
        acc = mulmod(acc, alpha, p) + gate;
        uint256 num_out = ((delta + (0 + (1 * v[18]))) + (delta + (0 + (1 * v[26]))));
        gate = num_out;
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 den_out = mulmod((delta + (0 + (1 * v[11]))), (delta + (0 + (1 * v[17]))), p);
        uint256 gate = den_out;
        acc = mulmod(acc, alpha, p) + gate;
        uint256 num_out = ((delta + (0 + (1 * v[11]))) + (delta + (0 + (1 * v[17]))));
        gate = num_out;
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 den_out = mulmod((delta + (0 + (1 * v[88]))), (delta + (0 + (1 * v[10]))), p);
        uint256 gate = den_out;
        acc = mulmod(acc, alpha, p) + gate;
        uint256 num_out = ((delta + (0 + (1 * v[88]))) + (delta + (0 + (1 * v[10]))));
        gate = num_out;
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 den_out = mulmod((delta + (0 + (1 * v[20]))), (delta + (0 + (1 * v[23]))), p);
        uint256 gate = den_out;
        acc = mulmod(acc, alpha, p) + gate;
        uint256 num_out = ((delta + (0 + (1 * v[20]))) + (delta + (0 + (1 * v[23]))));
        gate = num_out;
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 den_out = mulmod((delta + (0 + (1 * v[86]))), (delta + (0 + (1 * v[19]))), p);
        uint256 gate = den_out;
        acc = mulmod(acc, alpha, p) + gate;
        uint256 num_out = ((delta + (0 + (1 * v[86]))) + (delta + (0 + (1 * v[19]))));
        gate = num_out;
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 den_out = mulmod((delta + v[85]), (delta + cache[0]), p);
        uint256 gate = den_out;
        acc = mulmod(acc, alpha, p) + gate;
        uint256 num_out = ((delta + cache[0]) + (p - mulmod(v[100], (delta + v[85]), p)));
        gate = num_out;
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[80]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[79]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[78]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[77]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[42], (1 * v[57]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + ((mulmod(v[40], (1 * v[57]), p) + mulmod(v[57], (1 * v[64]), p)) + mulmod(v[58], (1 * v[68]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (mulmod(v[57], ((7864320 * v[82]) + (7864320 * ((2 * p) - v[3]))), p) + mulmod(v[58], (((1 * v[64]) + (7864320 * v[84])) + (7864320 * ((2 * p) - v[8]))), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (3 * v[57])) + mulmod(v[58], ((7864320 * v[82]) + (7864320 * ((2 * p) - v[3]))), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (9 * v[57])) + mulmod(v[42], (1 * v[58]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[76]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[75]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[74]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[73]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[42], (1 * v[57]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + ((((((mulmod(v[40], (1 * v[57]), p) + mulmod(v[52], (1 * v[26]), p)) + mulmod(v[53], (1 * v[26]), p)) + mulmod(v[54], (1 * v[26]), p)) + mulmod(v[55], (1 * v[26]), p)) + mulmod(v[57], (1 * v[64]), p)) + mulmod(v[58], (1 * v[67]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (((((mulmod(v[52], (1 * v[63]), p) + mulmod(v[53], (1 * v[63]), p)) + mulmod(v[54], (1 * v[63]), p)) + mulmod(v[55], (1 * v[63]), p)) + mulmod(v[57], (1 * v[82]), p)) + mulmod(v[58], ((1 * v[64]) + (1 * v[84])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (2 * v[57])) + ((((mulmod(v[52], (1 * v[88]), p) + mulmod(v[53], (1 * v[88]), p)) + mulmod(v[54], (1 * v[88]), p)) + mulmod(v[55], (1 * v[88]), p)) + mulmod(v[58], (1 * v[82]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (((((2 * v[52]) + (2 * v[53])) + (2 * v[54])) + (2 * v[55])) + (9 * v[57]))) + mulmod(v[42], (1 * v[58]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[72]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[71]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[70]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[69]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[42], (1 * v[57]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + ((mulmod(v[40], (1 * v[57]), p) + mulmod(v[57], (1 * v[64]), p)) + mulmod(v[58], (1 * v[66]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + ((((((mulmod(v[41], (1 * v[58]), p) + mulmod(v[52], (1 * v[66]), p)) + mulmod(v[53], (1 * v[66]), p)) + mulmod(v[54], (1 * v[66]), p)) + mulmod(v[55], (1 * v[66]), p)) + mulmod(v[57], ((7864320 * v[81]) + (7864320 * ((2 * p) - v[2]))), p)) + mulmod(v[58], ((7864320 * v[83]) + (7864320 * ((2 * p) - v[7]))), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (1 * v[57])) + (((((mulmod(v[42], ((((524288 * v[52]) + (524288 * v[53])) + (524288 * v[54])) + (524288 * v[55])), p) + mulmod(v[52], ((((131072 * v[60]) + (262144 * v[64])) + (65536 * v[65])) + (1 * v[8])), p)) + mulmod(v[53], ((((131072 * v[60]) + (262144 * v[64])) + (65536 * v[65])) + (1 * v[8])), p)) + mulmod(v[54], ((((131072 * v[60]) + (262144 * v[64])) + (65536 * v[65])) + (1 * v[8])), p)) + mulmod(v[55], ((((131072 * v[60]) + (262144 * v[64])) + (65536 * v[65])) + (1 * v[8])), p)) + mulmod(v[58], ((7864320 * v[81]) + (7864320 * ((2 * p) - v[2]))), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (((((31 * v[52]) + (31 * v[53])) + (31 * v[54])) + (31 * v[55])) + (9 * v[57]))) + mulmod(v[42], (1 * v[58]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[68]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[67]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[66]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[57], (1 * v[65]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + mulmod(v[42], (1 * v[57]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + ((mulmod(v[40], (1 * v[57]), p) + mulmod(v[57], (1 * v[64]), p)) + mulmod(v[58], (1 * v[65]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + ((((((mulmod(v[40], (1 * v[58]), p) + mulmod(v[52], (1 * v[65]), p)) + mulmod(v[53], (1 * v[65]), p)) + mulmod(v[54], (1 * v[65]), p)) + mulmod(v[55], (1 * v[65]), p)) + mulmod(v[57], (1 * v[81]), p)) + mulmod(v[58], (1 * v[83]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + ((((mulmod(v[52], (1 * v[3]), p) + mulmod(v[53], (1 * v[3]), p)) + mulmod(v[54], (1 * v[3]), p)) + mulmod(v[55], (1 * v[3]), p)) + mulmod(v[58], (1 * v[81]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + (((((5 * v[52]) + (5 * v[53])) + (5 * v[54])) + (5 * v[55])) + (9 * v[57]))) + mulmod(v[42], (1 * v[58]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (((mulmod(v[57], (1 * v[64]), p) + mulmod(v[8], (1 * v[93]), p)) + mulmod(v[9], ((1 * ((2 * p) - v[8])) + (1 * v[20])), p)) + mulmod(v[16], ((1 * ((2 * p) - v[8])) + (1 * v[20])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + ((((((((mulmod(v[52], (1 * v[64]), p) + mulmod(v[53], (1 * v[64]), p)) + mulmod(v[54], (1 * v[64]), p)) + mulmod(v[55], (1 * v[64]), p)) + mulmod(v[57], ((7864320 * v[83]) + (7864320 * ((2 * p) - v[7]))), p)) + mulmod(v[58], (1 * v[64]), p)) + mulmod(v[7], (1 * v[93]), p)) + mulmod(v[9], ((1 * ((2 * p) - v[7])) + (1 * v[19])), p)) + mulmod(v[16], ((1 * ((2 * p) - v[7])) + (1 * v[19])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + 0) + (((((((mulmod(v[41], (1 * v[58]), p) + mulmod(v[52], ((1 * v[85]) + (1 * v[86])), p)) + mulmod(v[53], ((1 * v[85]) + (1 * v[86])), p)) + mulmod(v[54], ((1 * v[85]) + (1 * v[86])), p)) + mulmod(v[55], ((1 * v[85]) + (1 * v[86])), p)) + mulmod(v[57], (1 * v[83]), p)) + mulmod(v[64], (1 * v[93]), p)) + mulmod(v[65], (65536 * v[93]), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + ((((((1 * v[52]) + (1 * v[53])) + (1 * v[54])) + (1 * v[55])) + (8 * v[57])) + (3 * v[58]))) + mulmod(v[21], (34 * v[93]), p));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = ((0 + ((64 * ((2 * p) - v[9])) + (64 * ((2 * p) - v[16])))) + (mulmod(v[9], ((65536 * v[61]) + (1 * v[65])), p) + mulmod(v[16], ((65536 * v[61]) + (1 * v[65])), p)));
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 shared = ((mc[6] + 1) + mulmod(mc[0], cache[2], p));
        uint256 lhs = (shared + (mulmod(mc[1], (cache[3] + 0), p) + memrelHigh(v[32], v[33], v[30], v[31], mc, p)));
        uint256 rhs = (shared + (mulmod(mc[1], (cache[3] + 1024), p) + memrelHigh(v[36], v[37], v[34], v[35], mc, p)));
        uint256 gate = mulmod(lhs, rhs, p);
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 shared = ((mc[6] + 1) + mulmod(mc[0], cache[2], p));
        uint256 lhs = (shared + (mulmod(mc[1], (cache[3] + 0), p) + 0));
        uint256 rhs = (shared + (mulmod(mc[1], (cache[3] + 1024), p) + 0));
        uint256 gate = mulmod(lhs, rhs, p);
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 lhs = memrel(v[16], v[17], v[18], (2 + v[24]), v[25], v[19], v[20], mc, p);
        uint256 rhs = memrel(2, 0, 0, (0 + v[28]), v[29], v[26], v[27], mc, p);
        uint256 gate = mulmod(lhs, rhs, p);
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 lhs = memrel(v[16], v[17], v[18], (0 + v[12]), v[13], v[14], v[15], mc, p);
        uint256 rhs = memrel(2, 0, 0, (0 + v[24]), v[25], v[22], v[23], mc, p);
        uint256 gate = mulmod(lhs, rhs, p);
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 lhs = memrel(0, v[4], 0, (0 + v[24]), v[25], v[2], v[3], mc, p);
        uint256 rhs = memrel(v[9], v[10], v[11], (1 + v[24]), v[25], v[7], v[8], mc, p);
        uint256 gate = mulmod(lhs, rhs, p);
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 lhs = memrel(0, v[4], 0, (0 + v[0]), v[1], v[2], v[3], mc, p);
        uint256 rhs = memrel(v[9], v[10], v[11], (0 + v[5]), v[6], v[7], v[8], mc, p);
        uint256 gate = mulmod(lhs, rhs, p);
        acc = mulmod(acc, alpha, p) + gate;
    }
    {
        uint256 gate = v[21];
        acc = mulmod(acc, alpha, p) + gate;
    }
    }
}

// Solve one linearly-appearing point so acc*eq_scale == claim (i.e. acc == target).
// With every other point fixed, acc is linear in v[k] unless v[k] is squared
// (booleanity gates); a 3-point finite-difference test skips those and picks the
// first index whose acc is affine with nonzero slope.
function patch_layer0(
    uint256[] memory vals,
    uint256 alpha,
    uint256[7] memory mc,
    uint256 beta,
    uint256 delta,
    uint256[24] memory point,
    uint256 target
) pure {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    for (uint256 k = 0; k < 113; ++k) {
        uint256 save = vals[k];
        vals[k] = 0; uint256 a0 = circuit_layer0_acc(vals, alpha, mc, beta, delta, point) % p;
        vals[k] = 1; uint256 a1 = circuit_layer0_acc(vals, alpha, mc, beta, delta, point) % p;
        vals[k] = 2; uint256 a2 = circuit_layer0_acc(vals, alpha, mc, beta, delta, point) % p;
        uint256 d1 = addmod(a1, p - a0, p);
        uint256 d2 = addmod(a2, p - a1, p);
        if (d1 != 0 && d1 == d2) { // affine in v[k] with nonzero slope
            vals[k] = mulmod(addmod(target, p - a0, p), modInv(d1, p), p);
            return;
        }
        vals[k] = save;
    }
    revert("layer0: no linear pivot point found");
}

// Mirrors sumcheck_circuit_layer0: 24 eq-deferred sumcheck rounds (solving c0
// each round) then a 113-point check folded as acc*eq_scale == claim.
function generate_circuit_layer0(
    bytes memory out,
    bytes32 state,
    uint256 claim,
    uint256 alpha,
    uint256[24] memory zpoint,
    bytes32 coeff_seed,
    uint256 beta,
    uint256 delta,
    uint256[7] memory mc
) pure returns (bytes memory, bytes32, uint256, uint256) {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    uint256 eq_scale;
    (out, state, claim, eq_scale) = generate_circuit_sumcheck(out, state, claim, zpoint, coeff_seed);
    // After the sumcheck, zpoint[0..23] holds layer-0's round challenges — the
    // point the cache virtual-polys (rangecheck / inits-teardowns) evaluate at.
    uint256 target = mulmod(claim, modInv(eq_scale, p), p);
    uint256[] memory vals = new uint256[](113);
    for (uint256 i = 0; i < 113; ++i) {
        vals[i] = uint256(keccak256(abi.encodePacked(coeff_seed, uint8(4), i))) % p;
    }
    patch_layer0(vals, alpha, mc, beta, delta, zpoint, target);
    bytes memory pointData = serialize_u128s(vals);
    out = abi.encodePacked(out, pointData);
    state = keccak256(abi.encodePacked(state, pointData));
    alpha = uint256(state) >> 128;
    claim = fold_claims(vals, alpha);
    return (out, state, claim, alpha);
}
