// BACKUP of the 1pass compression experiment (strategy A: per-side walk +
// deferred x4 fold via helper frames; -8.0% compress_gas on solx vs 2pass,
// passes all six stats.sh configs). Contracts renamed *2 so this file can
// coexist with gkr.sol under forge. Variants 2pass/1pass/1pass_fused are
// side by side; the gkr_expansion driver selects sumcheck_compress_1pass.
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.24;

contract GKRVerifier2 {
    uint256 constant ROUNDS = 200;
    uint256 constant P = 0xffffffffffffffffffffffffffffff61;
    uint256 constant MASK = 0xffffffffffffffffffffffffffffffff;
    // FOR TESTING PURPOSES
    uint256 constant GKR_INIT_CLAIM = 113722159391240751244870626465187757509;
    uint256 constant GKR_INIT_PTR = 2048;
    uint256 constant GKR_INIT_ALPHA = 24476944051572811188683507143397781588;
    uint256 constant GKR_INIT_SEED = 0xce46387e7b660cd47da6c27c09c76886126a1683dd762f5abed0eae149fab054;
    ///////////////////////
    uint256 constant GKR_INIT_POLYS = 8;
    uint256 constant GKR_INIT_POLY_SIZE = 16;
    uint256 constant GKR_INIT_FIELD_ELEMENTS = GKR_INIT_POLYS * GKR_INIT_POLY_SIZE;
    uint256 constant GKR_INIT_POLY_BYTES = 256; // = 16 * GKR_INIT_POLY_SIZE; literal because Yul rejects const expressions.
    uint256 constant GKR_INIT_BYTES = 2048; // = GKR_INIT_POLYS * GKR_INIT_POLY_SIZE * 16.
    uint256 constant GKR_COMPRESSION_POINTCHECK_POLY_BYTES = 64; // = 4 * 16.
    uint256 constant GKR_COMPRESSION_POINTCHECK_BYTES = 512; // = 8 * GKR_COMPRESSION_POINTCHECK_POLY_BYTES.
    // Byte addresses of the 16-word eq table materialized by gkr_init_fulleq_u256.
    // Base placed above transcript scratch [0, 2080) to avoid Yul stack spills
    // stomping the table under `assembly ("memory-safe")`. Workaround until we
    // switch to FMP-aware allocation (which would also shrink the touched region
    // and save ~270 gas of memory expansion).
    // uint256 constant GKR_INIT_EQ_PTR0  = 672;
    // uint256 constant GKR_INIT_EQ_PTR1  = 704;
    // uint256 constant GKR_INIT_EQ_PTR2  = 736;
    // uint256 constant GKR_INIT_EQ_PTR3  = 768;
    // uint256 constant GKR_INIT_EQ_PTR4  = 800;
    // uint256 constant GKR_INIT_EQ_PTR5  = 832;
    // uint256 constant GKR_INIT_EQ_PTR6  = 864;
    // uint256 constant GKR_INIT_EQ_PTR7  = 896;
    // uint256 constant GKR_INIT_EQ_PTR8  = 928;
    // uint256 constant GKR_INIT_EQ_PTR9  = 960;
    // uint256 constant GKR_INIT_EQ_PTR10 = 992;
    // uint256 constant GKR_INIT_EQ_PTR11 = 1024;
    // uint256 constant GKR_INIT_EQ_PTR12 = 1056;
    // uint256 constant GKR_INIT_EQ_PTR13 = 1088;
    // uint256 constant GKR_INIT_EQ_PTR14 = 1120;
    // uint256 constant GKR_INIT_EQ_PTR15 = 1152;
    uint256 constant GKR_INIT_EQ_PTR0  = 2496;
    uint256 constant GKR_INIT_EQ_PTR1  = 2528;
    uint256 constant GKR_INIT_EQ_PTR2  = 2560;
    uint256 constant GKR_INIT_EQ_PTR3  = 2592;
    uint256 constant GKR_INIT_EQ_PTR4  = 2624;
    uint256 constant GKR_INIT_EQ_PTR5  = 2656;
    uint256 constant GKR_INIT_EQ_PTR6  = 2688;
    uint256 constant GKR_INIT_EQ_PTR7  = 2720;
    uint256 constant GKR_INIT_EQ_PTR8  = 2752;
    uint256 constant GKR_INIT_EQ_PTR9  = 2784;
    uint256 constant GKR_INIT_EQ_PTR10 = 2816;
    uint256 constant GKR_INIT_EQ_PTR11 = 2848;
    uint256 constant GKR_INIT_EQ_PTR12 = 2880;
    uint256 constant GKR_INIT_EQ_PTR13 = 2912;
    uint256 constant GKR_INIT_EQ_PTR14 = 2944;
    uint256 constant GKR_INIT_EQ_PTR15 = 2976;
    uint256 constant POINT_PTR = 5568; // 24 coords: [5568, 6336), clear of the seed + recurring absorb scratch [5000, 5544) (transcript32to3 copies the 512B blob to SEED_PTR+32)
    // Scratch slot for stashing gas() across gkr_init_* calls. Without this,
    // a `let init_gas := gas()` Yul var can get spilled to memory and then
    // clobbered by stack pressure inside the init helpers (observed with
    // recursiverev_*), causing the returned init_gas to come back as garbage.
    // Placed well past EQ_PTR15 because solx spills aggressively past the eq
    // table into mem[2816..~4250); 4256 is the smallest offset where solx no
    // longer clobbers it across the gkr_init_inlinefold path.
    uint256 constant GKR_INIT_GAS_PTR  = 4256;
    uint256 constant GKR_COMPRESS_GAS_PTR = 4288;
    uint256 constant GKR_STREAMREV_CLAIM_PTR = 4512;
    uint256 constant CLAIM_PTR = 3000;
    // Base of the Fiat-Shamir transcript region. The seed lives in
    // mem[SEED_PTR..SEED_PTR+32) and the absorb scratch in
    // mem[SEED_PTR+32..SEED_PTR+96). All transcript helpers must use this
    // constant rather than hardcoded `0`/`32`/`64`, so the transcript layout
    // can later be relocated without auditing the whole script.
    uint256 constant SEED_PTR          = 5000;

    fallback() external {
        // uint256 variant = VARIANT;
        assembly {
        // assembly ("memory-safe") {
        // Proof/transcript bytes preserve logical stream order. Rust must append
        // fixed-width BE integer bytes: u32::to_be_bytes(), u64::to_be_bytes(),
        // u128::to_be_bytes(). 32-byte hashes/caps/roots are absorbed as raw bytes.
        // For u128 pairs calldata is [x0:16][x1:16], so x0 is shr(128, word)
        // and x1 is and(word, MASK). Smaller lanes follow the same BE packing rule
        // with larger shifts. Hash challenges are uint256 values already, so
        // and(seed, MASK) still means the numeric low 128 bits.
        function transcript_4to1_single(ptr) -> r {
            calldatacopy(add(SEED_PTR, 32), ptr, 64) // put to memory 4 coeffs from ptr, after SEED (prev hash, FS chain)
            let seed := keccak256(SEED_PTR, 96) // hash SEED + 4 coeffs to stack word
            mstore(SEED_PTR, seed) // immediately dump SEED
            r := and(seed, MASK)
        }

        function transcript_4to1_single_shr(ptr) -> r {
            calldatacopy(add(SEED_PTR, 32), ptr, 64) // put to memory 4 coeffs from ptr, after SEED (prev hash, FS chain)
            let seed := keccak256(SEED_PTR, 96) // hash SEED + 4 coeffs to stack word
            mstore(SEED_PTR, seed) // immediately dump SEED
            r := shr(128, seed)
        }

        function transcript_4to1_single_mod(ptr) -> r {
            calldatacopy(add(SEED_PTR, 32), ptr, 64) // put to memory 4 coeffs from ptr, after SEED (prev hash, FS chain)
            let seed := keccak256(SEED_PTR, 96) // hash SEED + 4 coeffs to stack word
            mstore(SEED_PTR, seed) // immediately dump SEED
            r := mod(seed, P)
        }

        function transcript_4to1_dual(w0, w1) -> r {
            // put to memory 4 coeffs from w0, w1, after SEED (prev hash, FS chain)
            mstore(add(SEED_PTR, 64), w1)
            mstore(add(SEED_PTR, 32), w0)
            let seed := keccak256(SEED_PTR, 96) // hash SEED + 4 coeffs to stack word
            mstore(SEED_PTR, seed) // immediately dump SEED
            r := and(seed, MASK)
        }

        function transcript_4to1_dual_shr(w0, w1) -> r {
            // put to memory 4 coeffs from w0, w1, after SEED (prev hash, FS chain)
            mstore(add(SEED_PTR, 64), w1)
            mstore(add(SEED_PTR, 32), w0)
            let seed := keccak256(SEED_PTR, 96) // hash SEED + 4 coeffs to stack word
            mstore(SEED_PTR, seed) // immediately dump SEED
            r := shr(128, seed)
        }

        function transcript_4to1_dual_mod(w0, w1) -> r {
            // put to memory 4 coeffs from w0, w1, after SEED (prev hash, FS chain)
            mstore(add(SEED_PTR, 64), w1)
            mstore(add(SEED_PTR, 32), w0)
            let seed := keccak256(SEED_PTR, 96) // hash SEED + 4 coeffs to stack word
            mstore(SEED_PTR, seed) // immediately dump SEED
            r := mod(seed, P)
        }

        // alpha is the batching challenge needed right after checking outputs
        function transcript128to5_once(ptr) -> z1, z2, z3, z4, alpha {
            calldatacopy(add(SEED_PTR, 32), ptr, GKR_INIT_BYTES)

            let seed := keccak256(SEED_PTR, add(32, GKR_INIT_BYTES))
            mstore(SEED_PTR, seed)
            z1 := and(seed, MASK)
            z2 := shr(128, seed)

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            z3 := and(seed, MASK)
            z4 := shr(128, seed)

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            alpha := and(seed, MASK)
        }

        function transcript128to5_2x64(ptr) -> z1, z2, z3, z4, alpha {
            calldatacopy(add(SEED_PTR, 32), ptr, 1024)
            let seed := keccak256(SEED_PTR, 1056)
            mstore(SEED_PTR, seed)

            calldatacopy(add(SEED_PTR, 32), add(ptr, 1024), 1024)
            seed := keccak256(SEED_PTR, 1056)
            mstore(SEED_PTR, seed)
            z1 := and(seed, MASK)
            z2 := shr(128, seed)

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            z3 := and(seed, MASK)
            z4 := shr(128, seed)

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            alpha := and(seed, MASK)
        }

        function transcript128to5_4x32(ptr) -> z1, z2, z3, z4, alpha {
            calldatacopy(add(SEED_PTR, 32), ptr, 512)
            let seed := keccak256(SEED_PTR, 544)
            mstore(SEED_PTR, seed)

            calldatacopy(add(SEED_PTR, 32), add(ptr, 512), 512)
            seed := keccak256(SEED_PTR, 544)
            mstore(SEED_PTR, seed)

            calldatacopy(add(SEED_PTR, 32), add(ptr, 1024), 512)
            seed := keccak256(SEED_PTR, 544)
            mstore(SEED_PTR, seed)

            calldatacopy(add(SEED_PTR, 32), add(ptr, 1536), 512)
            seed := keccak256(SEED_PTR, 544)
            mstore(SEED_PTR, seed)
            z1 := and(seed, MASK)
            z2 := shr(128, seed)

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            z3 := and(seed, MASK)
            z4 := shr(128, seed)

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            alpha := and(seed, MASK)
        }

        // alpha is the batching challenge needed right folding point claims
        function transcript32to3(ptr) -> z1, z2, alpha {
            calldatacopy(add(SEED_PTR, 32), ptr, GKR_COMPRESSION_POINTCHECK_BYTES)

            let seed := keccak256(SEED_PTR, add(32, GKR_COMPRESSION_POINTCHECK_BYTES))
            mstore(SEED_PTR, seed)
            z1 := and(seed, MASK)
            z2 := shr(128, seed)

            seed := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, seed)
            alpha := and(seed, MASK)
        }

        function store_eq16_crossproduct_u256_formula(z1, z2, z3, z4) {
            let p34 := mulmod(z3, z4, P)
            let e0 := sub(add(add(1, p34), mul(3, P)), add(z3, z4))
            let e1 := sub(add(z4, P), p34)
            let e2 := sub(add(z3, P), p34)
            let e3 := p34

            let p12 := mulmod(z1, z2, P)
            // 4 distinct column factors — avoid reassigning a single `t` variable
            // so the Rematerialiser sees 4 independent values rather than one
            // live-across var. Saves ~880 init gas on solc; no effect on solx.
            let t0 := sub(add(add(1, p12), mul(3, P)), add(z1, z2))
            let t1 := sub(add(z2, P), p12)
            let t2 := sub(add(z1, P), p12)
            // t3 = p12 (used directly)
            mstore(GKR_INIT_EQ_PTR0,  mulmod(e0, t0, P))
            mstore(GKR_INIT_EQ_PTR1,  mulmod(e1, t0, P))
            mstore(GKR_INIT_EQ_PTR2,  mulmod(e2, t0, P))
            mstore(GKR_INIT_EQ_PTR3,  mulmod(e3, t0, P))
            mstore(GKR_INIT_EQ_PTR4,  mulmod(e0, t1, P))
            mstore(GKR_INIT_EQ_PTR5,  mulmod(e1, t1, P))
            mstore(GKR_INIT_EQ_PTR6,  mulmod(e2, t1, P))
            mstore(GKR_INIT_EQ_PTR7,  mulmod(e3, t1, P))
            mstore(GKR_INIT_EQ_PTR8,  mulmod(e0, t2, P))
            mstore(GKR_INIT_EQ_PTR9,  mulmod(e1, t2, P))
            mstore(GKR_INIT_EQ_PTR10, mulmod(e2, t2, P))
            mstore(GKR_INIT_EQ_PTR11, mulmod(e3, t2, P))
            mstore(GKR_INIT_EQ_PTR12, mulmod(e0, p12, P))
            mstore(GKR_INIT_EQ_PTR13, mulmod(e1, p12, P))
            mstore(GKR_INIT_EQ_PTR14, mulmod(e2, p12, P))
            mstore(GKR_INIT_EQ_PTR15, mulmod(e3, p12, P))
        }

        function store_eq16_crossproduct_u256_nz(z1, z2, z3, z4) {
            let nz1 := sub(add(1, mul(2, P)), z1)
            let nz2 := sub(add(1, mul(2, P)), z2)
            let nz3 := sub(add(1, mul(2, P)), z3)
            let nz4 := sub(add(1, mul(2, P)), z4)

            let e0 := mulmod(nz4, nz3, P)
            let e1 := mulmod(z4, nz3, P)
            let e2 := mulmod(nz4, z3, P)
            let e3 := mulmod(z4, z3, P)

            let t := mulmod(nz2, nz1, P)
            mstore(GKR_INIT_EQ_PTR0,  mulmod(e0, t, P))
            mstore(GKR_INIT_EQ_PTR1,  mulmod(e1, t, P))
            mstore(GKR_INIT_EQ_PTR2,  mulmod(e2, t, P))
            mstore(GKR_INIT_EQ_PTR3,  mulmod(e3, t, P))

            t := mulmod(z2, nz1, P)
            mstore(GKR_INIT_EQ_PTR4,  mulmod(e0, t, P))
            mstore(GKR_INIT_EQ_PTR5,  mulmod(e1, t, P))
            mstore(GKR_INIT_EQ_PTR6,  mulmod(e2, t, P))
            mstore(GKR_INIT_EQ_PTR7,  mulmod(e3, t, P))

            t := mulmod(nz2, z1, P)
            mstore(GKR_INIT_EQ_PTR8,  mulmod(e0, t, P))
            mstore(GKR_INIT_EQ_PTR9,  mulmod(e1, t, P))
            mstore(GKR_INIT_EQ_PTR10, mulmod(e2, t, P))
            mstore(GKR_INIT_EQ_PTR11, mulmod(e3, t, P))

            t := mulmod(z2, z1, P)
            mstore(GKR_INIT_EQ_PTR12, mulmod(e0, t, P))
            mstore(GKR_INIT_EQ_PTR13, mulmod(e1, t, P))
            mstore(GKR_INIT_EQ_PTR14, mulmod(e2, t, P))
            mstore(GKR_INIT_EQ_PTR15, mulmod(e3, t, P))
        }

        function store_eq16_crossproduct_u128_formula(z1, z2, z3, z4) {
            let p34 := mulmod(z3, z4, P)
            let e0 := sub(add(add(1, p34), mul(3, P)), add(z3, z4))
            let e1 := sub(add(z4, P), p34)
            let e2 := sub(add(z3, P), p34)
            let e3 := p34

            let p12 := mulmod(z1, z2, P)
            // 4 distinct column factors — same SSA-style pattern as the u256
            // formula. Avoids reassigning `t` so the optimizer keeps each
            // single-use value as its own short-lived stack slot.
            let t0 := sub(add(add(1, p12), mul(3, P)), add(z1, z2))
            let t1 := sub(add(z2, P), p12)
            let t2 := sub(add(z1, P), p12)
            // t3 = p12 (used directly)
            mstore(GKR_INIT_EQ_PTR0, or(shl(128, mulmod(e0, t0, P)), mulmod(e1, t0, P)))
            mstore(GKR_INIT_EQ_PTR1, or(shl(128, mulmod(e2, t0, P)), mulmod(e3, t0, P)))
            mstore(GKR_INIT_EQ_PTR2, or(shl(128, mulmod(e0, t1, P)), mulmod(e1, t1, P)))
            mstore(GKR_INIT_EQ_PTR3, or(shl(128, mulmod(e2, t1, P)), mulmod(e3, t1, P)))
            mstore(GKR_INIT_EQ_PTR4, or(shl(128, mulmod(e0, t2, P)), mulmod(e1, t2, P)))
            mstore(GKR_INIT_EQ_PTR5, or(shl(128, mulmod(e2, t2, P)), mulmod(e3, t2, P)))
            mstore(GKR_INIT_EQ_PTR6, or(shl(128, mulmod(e0, p12, P)), mulmod(e1, p12, P)))
            mstore(GKR_INIT_EQ_PTR7, or(shl(128, mulmod(e2, p12, P)), mulmod(e3, p12, P)))
        }

        function store_eq16_crossproduct_u128_nz(z1, z2, z3, z4) {
            let nz1 := sub(add(1, mul(2, P)), z1)
            let nz2 := sub(add(1, mul(2, P)), z2)
            let nz3 := sub(add(1, mul(2, P)), z3)
            let nz4 := sub(add(1, mul(2, P)), z4)

            let e0 := mulmod(nz4, nz3, P)
            let e1 := mulmod(z4, nz3, P)
            let e2 := mulmod(nz4, z3, P)
            let e3 := mulmod(z4, z3, P)

            let t := mulmod(nz2, nz1, P)
            mstore(GKR_INIT_EQ_PTR0, or(shl(128, mulmod(e0, t, P)), mulmod(e1, t, P)))
            mstore(GKR_INIT_EQ_PTR1, or(shl(128, mulmod(e2, t, P)), mulmod(e3, t, P)))

            t := mulmod(z2, nz1, P)
            mstore(GKR_INIT_EQ_PTR2, or(shl(128, mulmod(e0, t, P)), mulmod(e1, t, P)))
            mstore(GKR_INIT_EQ_PTR3, or(shl(128, mulmod(e2, t, P)), mulmod(e3, t, P)))

            t := mulmod(nz2, z1, P)
            mstore(GKR_INIT_EQ_PTR4, or(shl(128, mulmod(e0, t, P)), mulmod(e1, t, P)))
            mstore(GKR_INIT_EQ_PTR5, or(shl(128, mulmod(e2, t, P)), mulmod(e3, t, P)))

            t := mulmod(z2, z1, P)
            mstore(GKR_INIT_EQ_PTR6, or(shl(128, mulmod(e0, t, P)), mulmod(e1, t, P)))
            mstore(GKR_INIT_EQ_PTR7, or(shl(128, mulmod(e2, t, P)), mulmod(e3, t, P)))
        }

        function store_eq16_recursiverev_u256(z1, z2, z3, z4) {
            let e0 := sub(add(1, mul(2, P)), z4)
            let e1 := z4

            let e2 := mulmod(e0, z3, P)
            e0 := sub(add(e0, P), e2)
            let e3 := mulmod(e1, z3, P)
            e1 := sub(add(e1, P), e3)

            let e4 := mulmod(e0, z2, P)
            e0 := sub(add(e0, P), e4)
            let e5 := mulmod(e1, z2, P)
            e1 := sub(add(e1, P), e5)
            let e6 := mulmod(e2, z2, P)
            e2 := sub(add(e2, P), e6)
            let e7 := mulmod(e3, z2, P)
            e3 := sub(add(e3, P), e7)

            let e8 := mulmod(e0, z1, P)
            e0 := sub(add(e0, P), e8)
            mstore(GKR_INIT_EQ_PTR0,  e0)
            mstore(GKR_INIT_EQ_PTR8,  e8)
            e8 := mulmod(e1, z1, P)
            e1 := sub(add(e1, P), e8)
            mstore(GKR_INIT_EQ_PTR1,  e1)
            mstore(GKR_INIT_EQ_PTR9,  e8)
            e8 := mulmod(e2, z1, P)
            e2 := sub(add(e2, P), e8)
            mstore(GKR_INIT_EQ_PTR2,  e2)
            mstore(GKR_INIT_EQ_PTR10, e8)
            e8 := mulmod(e3, z1, P)
            e3 := sub(add(e3, P), e8)
            mstore(GKR_INIT_EQ_PTR3,  e3)
            mstore(GKR_INIT_EQ_PTR11, e8)
            e8 := mulmod(e4, z1, P)
            e4 := sub(add(e4, P), e8)
            mstore(GKR_INIT_EQ_PTR4,  e4)
            mstore(GKR_INIT_EQ_PTR12, e8)
            e8 := mulmod(e5, z1, P)
            e5 := sub(add(e5, P), e8)
            mstore(GKR_INIT_EQ_PTR5,  e5)
            mstore(GKR_INIT_EQ_PTR13, e8)
            e8 := mulmod(e6, z1, P)
            e6 := sub(add(e6, P), e8)
            mstore(GKR_INIT_EQ_PTR6,  e6)
            mstore(GKR_INIT_EQ_PTR14, e8)
            e8 := mulmod(e7, z1, P)
            e7 := sub(add(e7, P), e8)
            mstore(GKR_INIT_EQ_PTR7,  e7)
            mstore(GKR_INIT_EQ_PTR15, e8)
        }

        function store_eq16_recursiverev_u128(z1, z2, z3, z4) {
            let e0 := sub(add(1, mul(2, P)), z4)
            let e1 := z4

            let e2 := mulmod(e0, z3, P)
            e0 := sub(add(e0, P), e2)
            let e3 := mulmod(e1, z3, P)
            e1 := sub(add(e1, P), e3)

            let e4 := mulmod(e0, z2, P)
            e0 := sub(add(e0, P), e4)
            let e5 := mulmod(e1, z2, P)
            e1 := sub(add(e1, P), e5)
            let e6 := mulmod(e2, z2, P)
            e2 := sub(add(e2, P), e6)
            let e7 := mulmod(e3, z2, P)
            e3 := sub(add(e3, P), e7)

            let e8 := mulmod(e0, z1, P)
            let e9 := mulmod(e1, z1, P)
            e0 := mod(sub(add(e0, P), e8), P)
            e1 := mod(sub(add(e1, P), e9), P)
            mstore(GKR_INIT_EQ_PTR0, or(shl(128, e0), e1))
            mstore(GKR_INIT_EQ_PTR4, or(shl(128, e8), e9))

            e8 := mulmod(e2, z1, P)
            e9 := mulmod(e3, z1, P)
            e2 := mod(sub(add(e2, P), e8), P)
            e3 := mod(sub(add(e3, P), e9), P)
            mstore(GKR_INIT_EQ_PTR1, or(shl(128, e2), e3))
            mstore(GKR_INIT_EQ_PTR5, or(shl(128, e8), e9))

            e8 := mulmod(e4, z1, P)
            e9 := mulmod(e5, z1, P)
            e4 := mod(sub(add(e4, P), e8), P)
            e5 := mod(sub(add(e5, P), e9), P)
            mstore(GKR_INIT_EQ_PTR2, or(shl(128, e4), e5))
            mstore(GKR_INIT_EQ_PTR6, or(shl(128, e8), e9))

            e8 := mulmod(e6, z1, P)
            e9 := mulmod(e7, z1, P)
            e6 := mod(sub(add(e6, P), e8), P)
            e7 := mod(sub(add(e7, P), e9), P)
            mstore(GKR_INIT_EQ_PTR3, or(shl(128, e6), e7))
            mstore(GKR_INIT_EQ_PTR7, or(shl(128, e8), e9))
        }

        // TODO: eventually move ptr inside
        function acceval_grandproduct_u256(ptr) -> claim, acc {
            let word, el0, el1, eq0, eq1
            claim := 0
            acc := 1

            word := calldataload(ptr)
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR0)
            eq1 := mload(GKR_INIT_EQ_PTR1)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 32))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR2)
            eq1 := mload(GKR_INIT_EQ_PTR3)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 64))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR4)
            eq1 := mload(GKR_INIT_EQ_PTR5)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 96))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR6)
            eq1 := mload(GKR_INIT_EQ_PTR7)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 128))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR8)
            eq1 := mload(GKR_INIT_EQ_PTR9)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 160))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR10)
            eq1 := mload(GKR_INIT_EQ_PTR11)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 192))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR12)
            eq1 := mload(GKR_INIT_EQ_PTR13)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 224))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR14)
            eq1 := mload(GKR_INIT_EQ_PTR15)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))
        }
        // u128 variant: eq stored packed as (eq[2k] << 128) | eq[2k+1] in
        // EQ_PTR0..EQ_PTR7 (8 slots) by store_eq16_crossproduct_u128_* /
        // store_eq16_recursiverev_u128.
        function acceval_grandproduct_u128(ptr) -> claim, acc {
            let word, el0, el1, eq_word, eq0, eq1
            claim := 0
            acc := 1

            word := calldataload(ptr)
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR0)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 32))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR1)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 64))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR2)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 96))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR3)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 128))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR4)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 160))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR5)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 192))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR6)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))

            word := calldataload(add(ptr, 224))
            el0 := shr(128, word)
            el1 := and(word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR7)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            acc := mulmod(acc, el0, P)
            acc := mulmod(acc, el1, P)
            claim := add(claim, mulmod(eq0, el0, P))
            claim := add(claim, mulmod(eq1, el1, P))
        }
        // TODO: eventually move ptr inside
        function acceval_logup_u256(ptr) -> num_claim, den_claim {
            let num_word, den_word, num0, num1, den0, den1, num, den, eq0, eq1
            let num_acc := 0
            let den_acc := 1
            num_claim := 0
            den_claim := 0

            num_word := calldataload(ptr)
            den_word := calldataload(add(ptr, GKR_INIT_POLY_BYTES))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR0)
            eq1 := mload(GKR_INIT_EQ_PTR1)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 32))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 32)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR2)
            eq1 := mload(GKR_INIT_EQ_PTR3)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 64))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 64)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR4)
            eq1 := mload(GKR_INIT_EQ_PTR5)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 96))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 96)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR6)
            eq1 := mload(GKR_INIT_EQ_PTR7)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 128))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 128)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR8)
            eq1 := mload(GKR_INIT_EQ_PTR9)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 160))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 160)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR10)
            eq1 := mload(GKR_INIT_EQ_PTR11)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 192))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 192)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR12)
            eq1 := mload(GKR_INIT_EQ_PTR13)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 224))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 224)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR14)
            eq1 := mload(GKR_INIT_EQ_PTR15)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            if mod(num_acc, P) { revert(0, 0) }
            if iszero(den_acc) { revert(0, 0) }
        }
        // u128 variant: eq stored packed as (eq[2k] << 128) | eq[2k+1] in
        // EQ_PTR0..EQ_PTR7.
        function acceval_logup_u128(ptr) -> num_claim, den_claim {
            let num_word, den_word, num0, num1, den0, den1, num, den, eq_word, eq0, eq1
            let num_acc := 0
            let den_acc := 1
            num_claim := 0
            den_claim := 0

            num_word := calldataload(ptr)
            den_word := calldataload(add(ptr, GKR_INIT_POLY_BYTES))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR0)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 32))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 32)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR1)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 64))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 64)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR2)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 96))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 96)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR3)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 128))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 128)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR4)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 160))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 160)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR5)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 192))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 192)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR6)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            num_word := calldataload(add(ptr, 224))
            den_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 224)))
            num0 := shr(128, num_word)
            num1 := and(num_word, MASK)
            den0 := shr(128, den_word)
            den1 := and(den_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR7)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            num_claim := add(num_claim, mulmod(eq0, num0, P))
            num_claim := add(num_claim, mulmod(eq1, num1, P))
            den_claim := add(den_claim, mulmod(eq0, den0, P))
            den_claim := add(den_claim, mulmod(eq1, den1, P))
            num := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
            den := mulmod(den0, den1, P)
            num_acc := add(mulmod(num, den_acc, P), mulmod(num_acc, den, P))
            den_acc := mulmod(den_acc, den, P)

            if mod(num_acc, P) { revert(0, 0) }
            if iszero(den_acc) { revert(0, 0) }
        }
        // TODO: eventually move ptr inside
        function acceval_twoshuffles_u256(ptr) -> read_claim, write_claim {
            let read_word, write_word, read0, read1, write0, write1, eq0, eq1
            let read_acc := 1
            let write_acc := 1
            read_claim := 0
            write_claim := 0

            read_word := calldataload(ptr)
            write_word := calldataload(add(ptr, GKR_INIT_POLY_BYTES))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR0)
            eq1 := mload(GKR_INIT_EQ_PTR1)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 32))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 32)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR2)
            eq1 := mload(GKR_INIT_EQ_PTR3)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 64))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 64)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR4)
            eq1 := mload(GKR_INIT_EQ_PTR5)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 96))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 96)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR6)
            eq1 := mload(GKR_INIT_EQ_PTR7)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 128))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 128)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR8)
            eq1 := mload(GKR_INIT_EQ_PTR9)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 160))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 160)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR10)
            eq1 := mload(GKR_INIT_EQ_PTR11)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 192))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 192)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR12)
            eq1 := mload(GKR_INIT_EQ_PTR13)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 224))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 224)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq0 := mload(GKR_INIT_EQ_PTR14)
            eq1 := mload(GKR_INIT_EQ_PTR15)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            if iszero(eq(read_acc, write_acc)) { revert(0, 0) }
        }
        // u128 variant: eq stored packed as (eq[2k] << 128) | eq[2k+1] in
        // EQ_PTR0..EQ_PTR7.
        function acceval_twoshuffles_u128(ptr) -> read_claim, write_claim {
            let read_word, write_word, read0, read1, write0, write1, eq_word, eq0, eq1
            let read_acc := 1
            let write_acc := 1
            read_claim := 0
            write_claim := 0

            read_word := calldataload(ptr)
            write_word := calldataload(add(ptr, GKR_INIT_POLY_BYTES))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR0)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 32))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 32)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR1)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 64))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 64)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR2)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 96))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 96)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR3)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 128))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 128)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR4)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 160))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 160)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR5)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 192))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 192)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR6)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            read_word := calldataload(add(ptr, 224))
            write_word := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 224)))
            read0 := shr(128, read_word)
            read1 := and(read_word, MASK)
            write0 := shr(128, write_word)
            write1 := and(write_word, MASK)
            eq_word := mload(GKR_INIT_EQ_PTR7)
            eq0 := shr(128, eq_word)
            eq1 := and(eq_word, MASK)
            read_acc := mulmod(mulmod(read_acc, read0, P), read1, P)
            write_acc := mulmod(mulmod(write_acc, write0, P), write1, P)
            read_claim := add(read_claim, mulmod(eq0, read0, P))
            read_claim := add(read_claim, mulmod(eq1, read1, P))
            write_claim := add(write_claim, mulmod(eq0, write0, P))
            write_claim := add(write_claim, mulmod(eq1, write1, P))

            if iszero(eq(read_acc, write_acc)) { revert(0, 0) }
        }

        // Strategy 1a: absorb the whole init block, draw z1..z4 and alpha, then
        // materialize full eq[16] in memory as one 256-bit word per field element.
        // Eq order must match Rust make_eq_poly: expand z4, z3, z2, z1. After
        // eq is stored at 32..512, do a second calldata pass to fold the 8 init
        // polys and batch their evaluations with alpha into the initial claim.
        function gkr_init_fulleq_u256(ptr) -> next_ptr, claim, alpha {
            let z1, z2, z3, z4
            z1, z2, z3, z4, alpha := transcript128to5_once(ptr)
            // let z1, z2, z3, z4, alpha := transcript128to5_2x64(ptr)
            // let z1, z2, z3, z4, alpha := transcript128to5_4x32(ptr)

            // TODO: store_eq16 should directly return the first used values instead of only storing them.
            store_eq16_crossproduct_u256_formula(z1, z2, z3, z4)
            // store_eq16_crossproduct_u256_nz(z1, z2, z3, z4)
            // store_eq16_recursiverev_u256(z1, z2, z3, z4)


            // TODO: the two mods can be batched into one mod + maybe a sub with const*P
            // let read_claim,  read_acc  := acceval_grandproduct_u256(ptr)
            // let write_claim, write_acc := acceval_grandproduct_u256(add(ptr, GKR_INIT_POLY_BYTES))
            // if iszero(eq(read_acc, write_acc)) { revert(0, 0) }
            let read_claim, write_claim := acceval_twoshuffles_u256(ptr)
            let num1_claim, den1_claim := acceval_logup_u256(add(ptr, mul(GKR_INIT_POLY_BYTES, 2))) // u16
            let num2_claim, den2_claim := acceval_logup_u256(add(ptr, mul(GKR_INIT_POLY_BYTES, 4))) // u19
            let num3_claim, den3_claim := acceval_logup_u256(add(ptr, mul(GKR_INIT_POLY_BYTES, 6))) // generic





            claim := add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(den3_claim, alpha, P), num3_claim), alpha, P), den2_claim), alpha, P), num2_claim), alpha, P), den1_claim), alpha, P), num1_claim), alpha, P), write_claim), alpha, P), read_claim)
            next_ptr := add(ptr, GKR_INIT_BYTES)
        }

        // Strategy 1b: same full-eq strategy as u256, but store eq[16] packed as
        // two u128 field elements per memory word. This reduces memory footprint
        // but consumers must unpack or consume pairs when folding/accumulating.
        function gkr_init_fulleq_u128(ptr) -> next_ptr, claim, alpha {
            let z1, z2, z3, z4
            z1, z2, z3, z4, alpha := transcript128to5_once(ptr)
            // z1, z2, z3, z4, alpha := transcript128to5_2x64(ptr)
            // z1, z2, z3, z4, alpha := transcript128to5_4x32(ptr)

            // TODO: store_eq16 should directly return the first used values instead of only storing them.
            // Both crossproduct_u128_{formula,nz} are currently broken when
            // combined with the inlined `acceval_logup_u128` × 3 below:
            //   - solc: hits Yul "stack too deep" at compile time — the
            //     compiler can't allocate the ~24 simultaneously-live
            //     `eq_word` SSA versions across the 3 inlined logup calls.
            //     Scoping `eq_word` per iteration was tried and didn't help.
            //   - solx: compiles fine (LLVM has no stack-too-deep), but at
            //     runtime the eq table is clobbered by solx's spills,
            //     producing wrong eq values and "verify failed".
            // `recursiverev_u128` works on both compilers — prefer that for now.
            // store_eq16_crossproduct_u128_formula(z1, z2, z3, z4) // BROKEN, see comment above
            // store_eq16_crossproduct_u128_nz(z1, z2, z3, z4)      // BROKEN, see comment above
            store_eq16_recursiverev_u128(z1, z2, z3, z4)

            let read_claim, write_claim := acceval_twoshuffles_u128(ptr)
            let num1_claim, den1_claim := acceval_logup_u128(add(ptr, mul(GKR_INIT_POLY_BYTES, 2)))
            let num2_claim, den2_claim := acceval_logup_u128(add(ptr, mul(GKR_INIT_POLY_BYTES, 4)))
            let num3_claim, den3_claim := acceval_logup_u128(add(ptr, mul(GKR_INIT_POLY_BYTES, 6)))

            claim := add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(den3_claim, alpha, P), num3_claim), alpha, P), den2_claim), alpha, P), num2_claim), alpha, P), den1_claim), alpha, P), num1_claim), alpha, P), write_claim), alpha, P), read_claim)
            next_ptr := add(ptr, GKR_INIT_BYTES)
        }

        function acceval_inlinefold_simple_lowhigh(ptr, z1, z2, z3, z4, alpha) -> claim {
            // strategy 2b: name all poly values in parallel and all instances of elements, let compiler fully control streaming
            // READ
            let read_word0 := calldataload(ptr)
            let read_word1 := calldataload(add(ptr, 32))
            let read_word2 := calldataload(add(ptr, 64))
            let read_word3 := calldataload(add(ptr, 96))
            let read_word4 := calldataload(add(ptr, 128))
            let read_word5 := calldataload(add(ptr, 160))
            let read_word6 := calldataload(add(ptr, 192))
            let read_word7 := calldataload(add(ptr, 224))
            let read0 := shr(128, read_word0)
            let read1 := and(read_word0, MASK)
            let read2 := shr(128, read_word1)
            let read3 := and(read_word1, MASK)
            let read4 := shr(128, read_word2)
            let read5 := and(read_word2, MASK)
            let read6 := shr(128, read_word3)
            let read7 := and(read_word3, MASK)
            let read8 := shr(128, read_word4)
            let read9 := and(read_word4, MASK)
            let read10 := shr(128, read_word5)
            let read11 := and(read_word5, MASK)
            let read12 := shr(128, read_word6)
            let read13 := and(read_word6, MASK)
            let read14 := shr(128, read_word7)
            let read15 := and(read_word7, MASK)
            let read_acc := mulmod(read0, read1, P)
            read_acc := mulmod(read_acc, read2, P)
            read_acc := mulmod(read_acc, read3, P)
            read_acc := mulmod(read_acc, read4, P)
            read_acc := mulmod(read_acc, read5, P)
            read_acc := mulmod(read_acc, read6, P)
            read_acc := mulmod(read_acc, read7, P)
            read_acc := mulmod(read_acc, read8, P)
            read_acc := mulmod(read_acc, read9, P)
            read_acc := mulmod(read_acc, read10, P)
            read_acc := mulmod(read_acc, read11, P)
            read_acc := mulmod(read_acc, read12, P)
            read_acc := mulmod(read_acc, read13, P)
            read_acc := mulmod(read_acc, read14, P)
            read_acc := mulmod(read_acc, read15, P)
            read0 := add(read0, mulmod(z1, sub(add(read8, mul(2, P)), read0), P))
            read1 := add(read1, mulmod(z1, sub(add(read9, mul(2, P)), read1), P))
            read2 := add(read2, mulmod(z1, sub(add(read10, mul(2, P)), read2), P))
            read3 := add(read3, mulmod(z1, sub(add(read11, mul(2, P)), read3), P))
            read4 := add(read4, mulmod(z1, sub(add(read12, mul(2, P)), read4), P))
            read5 := add(read5, mulmod(z1, sub(add(read13, mul(2, P)), read5), P))
            read6 := add(read6, mulmod(z1, sub(add(read14, mul(2, P)), read6), P))
            read7 := add(read7, mulmod(z1, sub(add(read15, mul(2, P)), read7), P))
            read0 := add(read0, mulmod(z2, sub(add(read4, mul(3, P)), read0), P))
            read1 := add(read1, mulmod(z2, sub(add(read5, mul(3, P)), read1), P))
            read2 := add(read2, mulmod(z2, sub(add(read6, mul(3, P)), read2), P))
            read3 := add(read3, mulmod(z2, sub(add(read7, mul(3, P)), read3), P))
            read0 := add(read0, mulmod(z3, sub(add(read2, mul(4, P)), read0), P))
            read1 := add(read1, mulmod(z3, sub(add(read3, mul(4, P)), read1), P))
            let read_claim := add(read0, mulmod(z4, sub(add(read1, mul(5, P)), read0), P))
            // WRITE
            let write_word0 := calldataload(add(ptr, GKR_INIT_POLY_BYTES))
            let write_word1 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 32)))
            let write_word2 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 64)))
            let write_word3 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 96)))
            let write_word4 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 128)))
            let write_word5 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 160)))
            let write_word6 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 192)))
            let write_word7 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 224)))
            let write0 := shr(128, write_word0)
            let write1 := and(write_word0, MASK)
            let write2 := shr(128, write_word1)
            let write3 := and(write_word1, MASK)
            let write4 := shr(128, write_word2)
            let write5 := and(write_word2, MASK)
            let write6 := shr(128, write_word3)
            let write7 := and(write_word3, MASK)
            let write8 := shr(128, write_word4)
            let write9 := and(write_word4, MASK)
            let write10 := shr(128, write_word5)
            let write11 := and(write_word5, MASK)
            let write12 := shr(128, write_word6)
            let write13 := and(write_word6, MASK)
            let write14 := shr(128, write_word7)
            let write15 := and(write_word7, MASK)
            let write_acc := mulmod(write0, write1, P)
            write_acc := mulmod(write_acc, write2, P)
            write_acc := mulmod(write_acc, write3, P)
            write_acc := mulmod(write_acc, write4, P)
            write_acc := mulmod(write_acc, write5, P)
            write_acc := mulmod(write_acc, write6, P)
            write_acc := mulmod(write_acc, write7, P)
            write_acc := mulmod(write_acc, write8, P)
            write_acc := mulmod(write_acc, write9, P)
            write_acc := mulmod(write_acc, write10, P)
            write_acc := mulmod(write_acc, write11, P)
            write_acc := mulmod(write_acc, write12, P)
            write_acc := mulmod(write_acc, write13, P)
            write_acc := mulmod(write_acc, write14, P)
            write_acc := mulmod(write_acc, write15, P)
            write0 := add(write0, mulmod(z1, sub(add(write8, mul(2, P)), write0), P))
            write1 := add(write1, mulmod(z1, sub(add(write9, mul(2, P)), write1), P))
            write2 := add(write2, mulmod(z1, sub(add(write10, mul(2, P)), write2), P))
            write3 := add(write3, mulmod(z1, sub(add(write11, mul(2, P)), write3), P))
            write4 := add(write4, mulmod(z1, sub(add(write12, mul(2, P)), write4), P))
            write5 := add(write5, mulmod(z1, sub(add(write13, mul(2, P)), write5), P))
            write6 := add(write6, mulmod(z1, sub(add(write14, mul(2, P)), write6), P))
            write7 := add(write7, mulmod(z1, sub(add(write15, mul(2, P)), write7), P))
            write0 := add(write0, mulmod(z2, sub(add(write4, mul(3, P)), write0), P))
            write1 := add(write1, mulmod(z2, sub(add(write5, mul(3, P)), write1), P))
            write2 := add(write2, mulmod(z2, sub(add(write6, mul(3, P)), write2), P))
            write3 := add(write3, mulmod(z2, sub(add(write7, mul(3, P)), write3), P))
            write0 := add(write0, mulmod(z3, sub(add(write2, mul(4, P)), write0), P))
            write1 := add(write1, mulmod(z3, sub(add(write3, mul(4, P)), write1), P))
            let write_claim := add(write0, mulmod(z4, sub(add(write1, mul(5, P)), write0), P))
            if iszero(eq(read_acc, write_acc)) { revert(0, 0) }
            // LOGUP1
            let num1_claim
            let den1_claim
            {
                let num_word0 := calldataload(add(ptr, mul(GKR_INIT_POLY_BYTES, 2)))
                let num_word1 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 32)))
                let num_word2 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 64)))
                let num_word3 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 96)))
                let num_word4 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 128)))
                let num_word5 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 160)))
                let num_word6 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 192)))
                let num_word7 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 224)))
                let den_word0 := calldataload(add(ptr, mul(GKR_INIT_POLY_BYTES, 3)))
                let den_word1 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 32)))
                let den_word2 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 64)))
                let den_word3 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 96)))
                let den_word4 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 128)))
                let den_word5 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 160)))
                let den_word6 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 192)))
                let den_word7 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 224)))
                let num0 := shr(128, num_word0)
                let num1 := and(num_word0, MASK)
                let num2 := shr(128, num_word1)
                let num3 := and(num_word1, MASK)
                let num4 := shr(128, num_word2)
                let num5 := and(num_word2, MASK)
                let num6 := shr(128, num_word3)
                let num7 := and(num_word3, MASK)
                let num8 := shr(128, num_word4)
                let num9 := and(num_word4, MASK)
                let num10 := shr(128, num_word5)
                let num11 := and(num_word5, MASK)
                let num12 := shr(128, num_word6)
                let num13 := and(num_word6, MASK)
                let num14 := shr(128, num_word7)
                let num15 := and(num_word7, MASK)
                let den0 := shr(128, den_word0)
                let den1 := and(den_word0, MASK)
                let den2 := shr(128, den_word1)
                let den3 := and(den_word1, MASK)
                let den4 := shr(128, den_word2)
                let den5 := and(den_word2, MASK)
                let den6 := shr(128, den_word3)
                let den7 := and(den_word3, MASK)
                let den8 := shr(128, den_word4)
                let den9 := and(den_word4, MASK)
                let den10 := shr(128, den_word5)
                let den11 := and(den_word5, MASK)
                let den12 := shr(128, den_word6)
                let den13 := and(den_word6, MASK)
                let den14 := shr(128, den_word7)
                let den15 := and(den_word7, MASK)
                let num_acc0 := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                let den_acc0 := mulmod(den0, den1, P)
                let num_acc1 := add(mulmod(num2, den3, P), mulmod(num3, den2, P))
                let den_acc1 := mulmod(den2, den3, P)
                let num_acc2 := add(mulmod(num4, den5, P), mulmod(num5, den4, P))
                let den_acc2 := mulmod(den4, den5, P)
                let num_acc3 := add(mulmod(num6, den7, P), mulmod(num7, den6, P))
                let den_acc3 := mulmod(den6, den7, P)
                let num_acc4 := add(mulmod(num8, den9, P), mulmod(num9, den8, P))
                let den_acc4 := mulmod(den8, den9, P)
                let num_acc5 := add(mulmod(num10, den11, P), mulmod(num11, den10, P))
                let den_acc5 := mulmod(den10, den11, P)
                let num_acc6 := add(mulmod(num12, den13, P), mulmod(num13, den12, P))
                let den_acc6 := mulmod(den12, den13, P)
                let num_acc7 := add(mulmod(num14, den15, P), mulmod(num15, den14, P))
                let den_acc7 := mulmod(den14, den15, P)
                num_acc0 := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                den_acc0 := mulmod(den_acc0, den_acc1, P)
                num_acc1 := add(mulmod(num_acc2, den_acc3, P), mulmod(num_acc3, den_acc2, P))
                den_acc1 := mulmod(den_acc2, den_acc3, P)
                num_acc2 := add(mulmod(num_acc4, den_acc5, P), mulmod(num_acc5, den_acc4, P))
                den_acc2 := mulmod(den_acc4, den_acc5, P)
                num_acc3 := add(mulmod(num_acc6, den_acc7, P), mulmod(num_acc7, den_acc6, P))
                den_acc3 := mulmod(den_acc6, den_acc7, P)
                num_acc0 := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                den_acc0 := mulmod(den_acc0, den_acc1, P)
                num_acc1 := add(mulmod(num_acc2, den_acc3, P), mulmod(num_acc3, den_acc2, P))
                den_acc1 := mulmod(den_acc2, den_acc3, P)
                let num_acc := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                let den_acc := mulmod(den_acc0, den_acc1, P)
                num0 := add(num0, mulmod(z1, sub(add(num8, mul(2, P)), num0), P))
                num1 := add(num1, mulmod(z1, sub(add(num9, mul(2, P)), num1), P))
                num2 := add(num2, mulmod(z1, sub(add(num10, mul(2, P)), num2), P))
                num3 := add(num3, mulmod(z1, sub(add(num11, mul(2, P)), num3), P))
                num4 := add(num4, mulmod(z1, sub(add(num12, mul(2, P)), num4), P))
                num5 := add(num5, mulmod(z1, sub(add(num13, mul(2, P)), num5), P))
                num6 := add(num6, mulmod(z1, sub(add(num14, mul(2, P)), num6), P))
                num7 := add(num7, mulmod(z1, sub(add(num15, mul(2, P)), num7), P))
                num0 := add(num0, mulmod(z2, sub(add(num4, mul(3, P)), num0), P))
                num1 := add(num1, mulmod(z2, sub(add(num5, mul(3, P)), num1), P))
                num2 := add(num2, mulmod(z2, sub(add(num6, mul(3, P)), num2), P))
                num3 := add(num3, mulmod(z2, sub(add(num7, mul(3, P)), num3), P))
                num0 := add(num0, mulmod(z3, sub(add(num2, mul(4, P)), num0), P))
                num1 := add(num1, mulmod(z3, sub(add(num3, mul(4, P)), num1), P))
                num1_claim := add(num0, mulmod(z4, sub(add(num1, mul(5, P)), num0), P))
                den0 := add(den0, mulmod(z1, sub(add(den8, mul(2, P)), den0), P))
                den1 := add(den1, mulmod(z1, sub(add(den9, mul(2, P)), den1), P))
                den2 := add(den2, mulmod(z1, sub(add(den10, mul(2, P)), den2), P))
                den3 := add(den3, mulmod(z1, sub(add(den11, mul(2, P)), den3), P))
                den4 := add(den4, mulmod(z1, sub(add(den12, mul(2, P)), den4), P))
                den5 := add(den5, mulmod(z1, sub(add(den13, mul(2, P)), den5), P))
                den6 := add(den6, mulmod(z1, sub(add(den14, mul(2, P)), den6), P))
                den7 := add(den7, mulmod(z1, sub(add(den15, mul(2, P)), den7), P))
                den0 := add(den0, mulmod(z2, sub(add(den4, mul(3, P)), den0), P))
                den1 := add(den1, mulmod(z2, sub(add(den5, mul(3, P)), den1), P))
                den2 := add(den2, mulmod(z2, sub(add(den6, mul(3, P)), den2), P))
                den3 := add(den3, mulmod(z2, sub(add(den7, mul(3, P)), den3), P))
                den0 := add(den0, mulmod(z3, sub(add(den2, mul(4, P)), den0), P))
                den1 := add(den1, mulmod(z3, sub(add(den3, mul(4, P)), den1), P))
                den1_claim := add(den0, mulmod(z4, sub(add(den1, mul(5, P)), den0), P))
                if mod(num_acc, P) { revert(0, 0) }
                if iszero(den_acc) { revert(0, 0) }
            }
            // LOGUP2
            let num2_claim
            let den2_claim
            {
                let num_word0 := calldataload(add(ptr, mul(GKR_INIT_POLY_BYTES, 4)))
                let num_word1 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 32)))
                let num_word2 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 64)))
                let num_word3 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 96)))
                let num_word4 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 128)))
                let num_word5 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 160)))
                let num_word6 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 192)))
                let num_word7 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 224)))
                let den_word0 := calldataload(add(ptr, mul(GKR_INIT_POLY_BYTES, 5)))
                let den_word1 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 32)))
                let den_word2 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 64)))
                let den_word3 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 96)))
                let den_word4 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 128)))
                let den_word5 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 160)))
                let den_word6 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 192)))
                let den_word7 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 224)))
                let num0 := shr(128, num_word0)
                let num1 := and(num_word0, MASK)
                let num2 := shr(128, num_word1)
                let num3 := and(num_word1, MASK)
                let num4 := shr(128, num_word2)
                let num5 := and(num_word2, MASK)
                let num6 := shr(128, num_word3)
                let num7 := and(num_word3, MASK)
                let num8 := shr(128, num_word4)
                let num9 := and(num_word4, MASK)
                let num10 := shr(128, num_word5)
                let num11 := and(num_word5, MASK)
                let num12 := shr(128, num_word6)
                let num13 := and(num_word6, MASK)
                let num14 := shr(128, num_word7)
                let num15 := and(num_word7, MASK)
                let den0 := shr(128, den_word0)
                let den1 := and(den_word0, MASK)
                let den2 := shr(128, den_word1)
                let den3 := and(den_word1, MASK)
                let den4 := shr(128, den_word2)
                let den5 := and(den_word2, MASK)
                let den6 := shr(128, den_word3)
                let den7 := and(den_word3, MASK)
                let den8 := shr(128, den_word4)
                let den9 := and(den_word4, MASK)
                let den10 := shr(128, den_word5)
                let den11 := and(den_word5, MASK)
                let den12 := shr(128, den_word6)
                let den13 := and(den_word6, MASK)
                let den14 := shr(128, den_word7)
                let den15 := and(den_word7, MASK)
                let num_acc0 := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                let den_acc0 := mulmod(den0, den1, P)
                let num_acc1 := add(mulmod(num2, den3, P), mulmod(num3, den2, P))
                let den_acc1 := mulmod(den2, den3, P)
                let num_acc2 := add(mulmod(num4, den5, P), mulmod(num5, den4, P))
                let den_acc2 := mulmod(den4, den5, P)
                let num_acc3 := add(mulmod(num6, den7, P), mulmod(num7, den6, P))
                let den_acc3 := mulmod(den6, den7, P)
                let num_acc4 := add(mulmod(num8, den9, P), mulmod(num9, den8, P))
                let den_acc4 := mulmod(den8, den9, P)
                let num_acc5 := add(mulmod(num10, den11, P), mulmod(num11, den10, P))
                let den_acc5 := mulmod(den10, den11, P)
                let num_acc6 := add(mulmod(num12, den13, P), mulmod(num13, den12, P))
                let den_acc6 := mulmod(den12, den13, P)
                let num_acc7 := add(mulmod(num14, den15, P), mulmod(num15, den14, P))
                let den_acc7 := mulmod(den14, den15, P)
                num_acc0 := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                den_acc0 := mulmod(den_acc0, den_acc1, P)
                num_acc1 := add(mulmod(num_acc2, den_acc3, P), mulmod(num_acc3, den_acc2, P))
                den_acc1 := mulmod(den_acc2, den_acc3, P)
                num_acc2 := add(mulmod(num_acc4, den_acc5, P), mulmod(num_acc5, den_acc4, P))
                den_acc2 := mulmod(den_acc4, den_acc5, P)
                num_acc3 := add(mulmod(num_acc6, den_acc7, P), mulmod(num_acc7, den_acc6, P))
                den_acc3 := mulmod(den_acc6, den_acc7, P)
                num_acc0 := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                den_acc0 := mulmod(den_acc0, den_acc1, P)
                num_acc1 := add(mulmod(num_acc2, den_acc3, P), mulmod(num_acc3, den_acc2, P))
                den_acc1 := mulmod(den_acc2, den_acc3, P)
                let num_acc := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                let den_acc := mulmod(den_acc0, den_acc1, P)
                num0 := add(num0, mulmod(z1, sub(add(num8, mul(2, P)), num0), P))
                num1 := add(num1, mulmod(z1, sub(add(num9, mul(2, P)), num1), P))
                num2 := add(num2, mulmod(z1, sub(add(num10, mul(2, P)), num2), P))
                num3 := add(num3, mulmod(z1, sub(add(num11, mul(2, P)), num3), P))
                num4 := add(num4, mulmod(z1, sub(add(num12, mul(2, P)), num4), P))
                num5 := add(num5, mulmod(z1, sub(add(num13, mul(2, P)), num5), P))
                num6 := add(num6, mulmod(z1, sub(add(num14, mul(2, P)), num6), P))
                num7 := add(num7, mulmod(z1, sub(add(num15, mul(2, P)), num7), P))
                num0 := add(num0, mulmod(z2, sub(add(num4, mul(3, P)), num0), P))
                num1 := add(num1, mulmod(z2, sub(add(num5, mul(3, P)), num1), P))
                num2 := add(num2, mulmod(z2, sub(add(num6, mul(3, P)), num2), P))
                num3 := add(num3, mulmod(z2, sub(add(num7, mul(3, P)), num3), P))
                num0 := add(num0, mulmod(z3, sub(add(num2, mul(4, P)), num0), P))
                num1 := add(num1, mulmod(z3, sub(add(num3, mul(4, P)), num1), P))
                num2_claim := add(num0, mulmod(z4, sub(add(num1, mul(5, P)), num0), P))
                den0 := add(den0, mulmod(z1, sub(add(den8, mul(2, P)), den0), P))
                den1 := add(den1, mulmod(z1, sub(add(den9, mul(2, P)), den1), P))
                den2 := add(den2, mulmod(z1, sub(add(den10, mul(2, P)), den2), P))
                den3 := add(den3, mulmod(z1, sub(add(den11, mul(2, P)), den3), P))
                den4 := add(den4, mulmod(z1, sub(add(den12, mul(2, P)), den4), P))
                den5 := add(den5, mulmod(z1, sub(add(den13, mul(2, P)), den5), P))
                den6 := add(den6, mulmod(z1, sub(add(den14, mul(2, P)), den6), P))
                den7 := add(den7, mulmod(z1, sub(add(den15, mul(2, P)), den7), P))
                den0 := add(den0, mulmod(z2, sub(add(den4, mul(3, P)), den0), P))
                den1 := add(den1, mulmod(z2, sub(add(den5, mul(3, P)), den1), P))
                den2 := add(den2, mulmod(z2, sub(add(den6, mul(3, P)), den2), P))
                den3 := add(den3, mulmod(z2, sub(add(den7, mul(3, P)), den3), P))
                den0 := add(den0, mulmod(z3, sub(add(den2, mul(4, P)), den0), P))
                den1 := add(den1, mulmod(z3, sub(add(den3, mul(4, P)), den1), P))
                den2_claim := add(den0, mulmod(z4, sub(add(den1, mul(5, P)), den0), P))
                if mod(num_acc, P) { revert(0, 0) }
                if iszero(den_acc) { revert(0, 0) }
            }
            // LOGUP3
            let num3_claim
            let den3_claim
            {
                let num_word0 := calldataload(add(ptr, mul(GKR_INIT_POLY_BYTES, 6)))
                let num_word1 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 32)))
                let num_word2 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 64)))
                let num_word3 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 96)))
                let num_word4 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 128)))
                let num_word5 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 160)))
                let num_word6 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 192)))
                let num_word7 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 224)))
                let den_word0 := calldataload(add(ptr, mul(GKR_INIT_POLY_BYTES, 7)))
                let den_word1 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 32)))
                let den_word2 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 64)))
                let den_word3 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 96)))
                let den_word4 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 128)))
                let den_word5 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 160)))
                let den_word6 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 192)))
                let den_word7 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 224)))
                let num0 := shr(128, num_word0)
                let num1 := and(num_word0, MASK)
                let num2 := shr(128, num_word1)
                let num3 := and(num_word1, MASK)
                let num4 := shr(128, num_word2)
                let num5 := and(num_word2, MASK)
                let num6 := shr(128, num_word3)
                let num7 := and(num_word3, MASK)
                let num8 := shr(128, num_word4)
                let num9 := and(num_word4, MASK)
                let num10 := shr(128, num_word5)
                let num11 := and(num_word5, MASK)
                let num12 := shr(128, num_word6)
                let num13 := and(num_word6, MASK)
                let num14 := shr(128, num_word7)
                let num15 := and(num_word7, MASK)
                let den0 := shr(128, den_word0)
                let den1 := and(den_word0, MASK)
                let den2 := shr(128, den_word1)
                let den3 := and(den_word1, MASK)
                let den4 := shr(128, den_word2)
                let den5 := and(den_word2, MASK)
                let den6 := shr(128, den_word3)
                let den7 := and(den_word3, MASK)
                let den8 := shr(128, den_word4)
                let den9 := and(den_word4, MASK)
                let den10 := shr(128, den_word5)
                let den11 := and(den_word5, MASK)
                let den12 := shr(128, den_word6)
                let den13 := and(den_word6, MASK)
                let den14 := shr(128, den_word7)
                let den15 := and(den_word7, MASK)
                let num_acc0 := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                let den_acc0 := mulmod(den0, den1, P)
                let num_acc1 := add(mulmod(num2, den3, P), mulmod(num3, den2, P))
                let den_acc1 := mulmod(den2, den3, P)
                let num_acc2 := add(mulmod(num4, den5, P), mulmod(num5, den4, P))
                let den_acc2 := mulmod(den4, den5, P)
                let num_acc3 := add(mulmod(num6, den7, P), mulmod(num7, den6, P))
                let den_acc3 := mulmod(den6, den7, P)
                let num_acc4 := add(mulmod(num8, den9, P), mulmod(num9, den8, P))
                let den_acc4 := mulmod(den8, den9, P)
                let num_acc5 := add(mulmod(num10, den11, P), mulmod(num11, den10, P))
                let den_acc5 := mulmod(den10, den11, P)
                let num_acc6 := add(mulmod(num12, den13, P), mulmod(num13, den12, P))
                let den_acc6 := mulmod(den12, den13, P)
                let num_acc7 := add(mulmod(num14, den15, P), mulmod(num15, den14, P))
                let den_acc7 := mulmod(den14, den15, P)
                num_acc0 := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                den_acc0 := mulmod(den_acc0, den_acc1, P)
                num_acc1 := add(mulmod(num_acc2, den_acc3, P), mulmod(num_acc3, den_acc2, P))
                den_acc1 := mulmod(den_acc2, den_acc3, P)
                num_acc2 := add(mulmod(num_acc4, den_acc5, P), mulmod(num_acc5, den_acc4, P))
                den_acc2 := mulmod(den_acc4, den_acc5, P)
                num_acc3 := add(mulmod(num_acc6, den_acc7, P), mulmod(num_acc7, den_acc6, P))
                den_acc3 := mulmod(den_acc6, den_acc7, P)
                num_acc0 := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                den_acc0 := mulmod(den_acc0, den_acc1, P)
                num_acc1 := add(mulmod(num_acc2, den_acc3, P), mulmod(num_acc3, den_acc2, P))
                den_acc1 := mulmod(den_acc2, den_acc3, P)
                let num_acc := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                let den_acc := mulmod(den_acc0, den_acc1, P)
                num0 := add(num0, mulmod(z1, sub(add(num8, mul(2, P)), num0), P))
                num1 := add(num1, mulmod(z1, sub(add(num9, mul(2, P)), num1), P))
                num2 := add(num2, mulmod(z1, sub(add(num10, mul(2, P)), num2), P))
                num3 := add(num3, mulmod(z1, sub(add(num11, mul(2, P)), num3), P))
                num4 := add(num4, mulmod(z1, sub(add(num12, mul(2, P)), num4), P))
                num5 := add(num5, mulmod(z1, sub(add(num13, mul(2, P)), num5), P))
                num6 := add(num6, mulmod(z1, sub(add(num14, mul(2, P)), num6), P))
                num7 := add(num7, mulmod(z1, sub(add(num15, mul(2, P)), num7), P))
                num0 := add(num0, mulmod(z2, sub(add(num4, mul(3, P)), num0), P))
                num1 := add(num1, mulmod(z2, sub(add(num5, mul(3, P)), num1), P))
                num2 := add(num2, mulmod(z2, sub(add(num6, mul(3, P)), num2), P))
                num3 := add(num3, mulmod(z2, sub(add(num7, mul(3, P)), num3), P))
                num0 := add(num0, mulmod(z3, sub(add(num2, mul(4, P)), num0), P))
                num1 := add(num1, mulmod(z3, sub(add(num3, mul(4, P)), num1), P))
                num3_claim := add(num0, mulmod(z4, sub(add(num1, mul(5, P)), num0), P))
                den0 := add(den0, mulmod(z1, sub(add(den8, mul(2, P)), den0), P))
                den1 := add(den1, mulmod(z1, sub(add(den9, mul(2, P)), den1), P))
                den2 := add(den2, mulmod(z1, sub(add(den10, mul(2, P)), den2), P))
                den3 := add(den3, mulmod(z1, sub(add(den11, mul(2, P)), den3), P))
                den4 := add(den4, mulmod(z1, sub(add(den12, mul(2, P)), den4), P))
                den5 := add(den5, mulmod(z1, sub(add(den13, mul(2, P)), den5), P))
                den6 := add(den6, mulmod(z1, sub(add(den14, mul(2, P)), den6), P))
                den7 := add(den7, mulmod(z1, sub(add(den15, mul(2, P)), den7), P))
                den0 := add(den0, mulmod(z2, sub(add(den4, mul(3, P)), den0), P))
                den1 := add(den1, mulmod(z2, sub(add(den5, mul(3, P)), den1), P))
                den2 := add(den2, mulmod(z2, sub(add(den6, mul(3, P)), den2), P))
                den3 := add(den3, mulmod(z2, sub(add(den7, mul(3, P)), den3), P))
                den0 := add(den0, mulmod(z3, sub(add(den2, mul(4, P)), den0), P))
                den1 := add(den1, mulmod(z3, sub(add(den3, mul(4, P)), den1), P))
                den3_claim := add(den0, mulmod(z4, sub(add(den1, mul(5, P)), den0), P))
                if mod(num_acc, P) { revert(0, 0) }
                if iszero(den_acc) { revert(0, 0) }
            }
            claim := add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(den3_claim, alpha, P), num3_claim), alpha, P), den2_claim), alpha, P), num2_claim), alpha, P), den1_claim), alpha, P), num1_claim), alpha, P), write_claim), alpha, P), read_claim)
        }
        function acceval_inlinefold_simple_evenodd(ptr, z1, z2, z3, z4, alpha) -> claim {
            // strategy 2b: name all poly values in parallel and all instances of elements, let compiler fully control streaming
            // READ
            let read_word0 := calldataload(ptr)
            let read_word1 := calldataload(add(ptr, 32))
            let read_word2 := calldataload(add(ptr, 64))
            let read_word3 := calldataload(add(ptr, 96))
            let read_word4 := calldataload(add(ptr, 128))
            let read_word5 := calldataload(add(ptr, 160))
            let read_word6 := calldataload(add(ptr, 192))
            let read_word7 := calldataload(add(ptr, 224))
            let read0 := shr(128, read_word0)
            let read1 := and(read_word0, MASK)
            let read2 := shr(128, read_word1)
            let read3 := and(read_word1, MASK)
            let read4 := shr(128, read_word2)
            let read5 := and(read_word2, MASK)
            let read6 := shr(128, read_word3)
            let read7 := and(read_word3, MASK)
            let read8 := shr(128, read_word4)
            let read9 := and(read_word4, MASK)
            let read10 := shr(128, read_word5)
            let read11 := and(read_word5, MASK)
            let read12 := shr(128, read_word6)
            let read13 := and(read_word6, MASK)
            let read14 := shr(128, read_word7)
            let read15 := and(read_word7, MASK)
            let read_acc := mulmod(read0, read1, P)
            read_acc := mulmod(read_acc, read2, P)
            read_acc := mulmod(read_acc, read3, P)
            read_acc := mulmod(read_acc, read4, P)
            read_acc := mulmod(read_acc, read5, P)
            read_acc := mulmod(read_acc, read6, P)
            read_acc := mulmod(read_acc, read7, P)
            read_acc := mulmod(read_acc, read8, P)
            read_acc := mulmod(read_acc, read9, P)
            read_acc := mulmod(read_acc, read10, P)
            read_acc := mulmod(read_acc, read11, P)
            read_acc := mulmod(read_acc, read12, P)
            read_acc := mulmod(read_acc, read13, P)
            read_acc := mulmod(read_acc, read14, P)
            read_acc := mulmod(read_acc, read15, P)
            read0 := add(read0, mulmod(z4, sub(add(read1, mul(2, P)), read0), P))
            read1 := add(read2, mulmod(z4, sub(add(read3, mul(2, P)), read2), P))
            read2 := add(read4, mulmod(z4, sub(add(read5, mul(2, P)), read4), P))
            read3 := add(read6, mulmod(z4, sub(add(read7, mul(2, P)), read6), P))
            read4 := add(read8, mulmod(z4, sub(add(read9, mul(2, P)), read8), P))
            read5 := add(read10, mulmod(z4, sub(add(read11, mul(2, P)), read10), P))
            read6 := add(read12, mulmod(z4, sub(add(read13, mul(2, P)), read12), P))
            read7 := add(read14, mulmod(z4, sub(add(read15, mul(2, P)), read14), P))
            read0 := add(read0, mulmod(z3, sub(add(read1, mul(3, P)), read0), P))
            read1 := add(read2, mulmod(z3, sub(add(read3, mul(3, P)), read2), P))
            read2 := add(read4, mulmod(z3, sub(add(read5, mul(3, P)), read4), P))
            read3 := add(read6, mulmod(z3, sub(add(read7, mul(3, P)), read6), P))
            read0 := add(read0, mulmod(z2, sub(add(read1, mul(4, P)), read0), P))
            read1 := add(read2, mulmod(z2, sub(add(read3, mul(4, P)), read2), P))
            let read_claim := add(read0, mulmod(z1, sub(add(read1, mul(5, P)), read0), P))
            // WRITE
            let write_word0 := calldataload(add(ptr, GKR_INIT_POLY_BYTES))
            let write_word1 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 32)))
            let write_word2 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 64)))
            let write_word3 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 96)))
            let write_word4 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 128)))
            let write_word5 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 160)))
            let write_word6 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 192)))
            let write_word7 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 224)))
            let write0 := shr(128, write_word0)
            let write1 := and(write_word0, MASK)
            let write2 := shr(128, write_word1)
            let write3 := and(write_word1, MASK)
            let write4 := shr(128, write_word2)
            let write5 := and(write_word2, MASK)
            let write6 := shr(128, write_word3)
            let write7 := and(write_word3, MASK)
            let write8 := shr(128, write_word4)
            let write9 := and(write_word4, MASK)
            let write10 := shr(128, write_word5)
            let write11 := and(write_word5, MASK)
            let write12 := shr(128, write_word6)
            let write13 := and(write_word6, MASK)
            let write14 := shr(128, write_word7)
            let write15 := and(write_word7, MASK)
            let write_acc := mulmod(write0, write1, P)
            write_acc := mulmod(write_acc, write2, P)
            write_acc := mulmod(write_acc, write3, P)
            write_acc := mulmod(write_acc, write4, P)
            write_acc := mulmod(write_acc, write5, P)
            write_acc := mulmod(write_acc, write6, P)
            write_acc := mulmod(write_acc, write7, P)
            write_acc := mulmod(write_acc, write8, P)
            write_acc := mulmod(write_acc, write9, P)
            write_acc := mulmod(write_acc, write10, P)
            write_acc := mulmod(write_acc, write11, P)
            write_acc := mulmod(write_acc, write12, P)
            write_acc := mulmod(write_acc, write13, P)
            write_acc := mulmod(write_acc, write14, P)
            write_acc := mulmod(write_acc, write15, P)
            write0 := add(write0, mulmod(z4, sub(add(write1, mul(2, P)), write0), P))
            write1 := add(write2, mulmod(z4, sub(add(write3, mul(2, P)), write2), P))
            write2 := add(write4, mulmod(z4, sub(add(write5, mul(2, P)), write4), P))
            write3 := add(write6, mulmod(z4, sub(add(write7, mul(2, P)), write6), P))
            write4 := add(write8, mulmod(z4, sub(add(write9, mul(2, P)), write8), P))
            write5 := add(write10, mulmod(z4, sub(add(write11, mul(2, P)), write10), P))
            write6 := add(write12, mulmod(z4, sub(add(write13, mul(2, P)), write12), P))
            write7 := add(write14, mulmod(z4, sub(add(write15, mul(2, P)), write14), P))
            write0 := add(write0, mulmod(z3, sub(add(write1, mul(3, P)), write0), P))
            write1 := add(write2, mulmod(z3, sub(add(write3, mul(3, P)), write2), P))
            write2 := add(write4, mulmod(z3, sub(add(write5, mul(3, P)), write4), P))
            write3 := add(write6, mulmod(z3, sub(add(write7, mul(3, P)), write6), P))
            write0 := add(write0, mulmod(z2, sub(add(write1, mul(4, P)), write0), P))
            write1 := add(write2, mulmod(z2, sub(add(write3, mul(4, P)), write2), P))
            let write_claim := add(write0, mulmod(z1, sub(add(write1, mul(5, P)), write0), P))
            if iszero(eq(read_acc, write_acc)) { revert(0, 0) }
            // LOGUP1
            let num1_claim
            let den1_claim
            {
                let num_word0 := calldataload(add(ptr, mul(GKR_INIT_POLY_BYTES, 2)))
                let num_word1 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 32)))
                let num_word2 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 64)))
                let num_word3 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 96)))
                let num_word4 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 128)))
                let num_word5 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 160)))
                let num_word6 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 192)))
                let num_word7 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 2), 224)))
                let den_word0 := calldataload(add(ptr, mul(GKR_INIT_POLY_BYTES, 3)))
                let den_word1 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 32)))
                let den_word2 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 64)))
                let den_word3 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 96)))
                let den_word4 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 128)))
                let den_word5 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 160)))
                let den_word6 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 192)))
                let den_word7 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 3), 224)))
                let num0 := shr(128, num_word0)
                let num1 := and(num_word0, MASK)
                let num2 := shr(128, num_word1)
                let num3 := and(num_word1, MASK)
                let num4 := shr(128, num_word2)
                let num5 := and(num_word2, MASK)
                let num6 := shr(128, num_word3)
                let num7 := and(num_word3, MASK)
                let num8 := shr(128, num_word4)
                let num9 := and(num_word4, MASK)
                let num10 := shr(128, num_word5)
                let num11 := and(num_word5, MASK)
                let num12 := shr(128, num_word6)
                let num13 := and(num_word6, MASK)
                let num14 := shr(128, num_word7)
                let num15 := and(num_word7, MASK)
                let den0 := shr(128, den_word0)
                let den1 := and(den_word0, MASK)
                let den2 := shr(128, den_word1)
                let den3 := and(den_word1, MASK)
                let den4 := shr(128, den_word2)
                let den5 := and(den_word2, MASK)
                let den6 := shr(128, den_word3)
                let den7 := and(den_word3, MASK)
                let den8 := shr(128, den_word4)
                let den9 := and(den_word4, MASK)
                let den10 := shr(128, den_word5)
                let den11 := and(den_word5, MASK)
                let den12 := shr(128, den_word6)
                let den13 := and(den_word6, MASK)
                let den14 := shr(128, den_word7)
                let den15 := and(den_word7, MASK)
                let num_acc0 := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                let den_acc0 := mulmod(den0, den1, P)
                let num_acc1 := add(mulmod(num2, den3, P), mulmod(num3, den2, P))
                let den_acc1 := mulmod(den2, den3, P)
                let num_acc2 := add(mulmod(num4, den5, P), mulmod(num5, den4, P))
                let den_acc2 := mulmod(den4, den5, P)
                let num_acc3 := add(mulmod(num6, den7, P), mulmod(num7, den6, P))
                let den_acc3 := mulmod(den6, den7, P)
                let num_acc4 := add(mulmod(num8, den9, P), mulmod(num9, den8, P))
                let den_acc4 := mulmod(den8, den9, P)
                let num_acc5 := add(mulmod(num10, den11, P), mulmod(num11, den10, P))
                let den_acc5 := mulmod(den10, den11, P)
                let num_acc6 := add(mulmod(num12, den13, P), mulmod(num13, den12, P))
                let den_acc6 := mulmod(den12, den13, P)
                let num_acc7 := add(mulmod(num14, den15, P), mulmod(num15, den14, P))
                let den_acc7 := mulmod(den14, den15, P)
                num_acc0 := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                den_acc0 := mulmod(den_acc0, den_acc1, P)
                num_acc1 := add(mulmod(num_acc2, den_acc3, P), mulmod(num_acc3, den_acc2, P))
                den_acc1 := mulmod(den_acc2, den_acc3, P)
                num_acc2 := add(mulmod(num_acc4, den_acc5, P), mulmod(num_acc5, den_acc4, P))
                den_acc2 := mulmod(den_acc4, den_acc5, P)
                num_acc3 := add(mulmod(num_acc6, den_acc7, P), mulmod(num_acc7, den_acc6, P))
                den_acc3 := mulmod(den_acc6, den_acc7, P)
                num_acc0 := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                den_acc0 := mulmod(den_acc0, den_acc1, P)
                num_acc1 := add(mulmod(num_acc2, den_acc3, P), mulmod(num_acc3, den_acc2, P))
                den_acc1 := mulmod(den_acc2, den_acc3, P)
                let num_acc := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                let den_acc := mulmod(den_acc0, den_acc1, P)
                num0 := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                num1 := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                num2 := add(num4, mulmod(z4, sub(add(num5, mul(2, P)), num4), P))
                num3 := add(num6, mulmod(z4, sub(add(num7, mul(2, P)), num6), P))
                num4 := add(num8, mulmod(z4, sub(add(num9, mul(2, P)), num8), P))
                num5 := add(num10, mulmod(z4, sub(add(num11, mul(2, P)), num10), P))
                num6 := add(num12, mulmod(z4, sub(add(num13, mul(2, P)), num12), P))
                num7 := add(num14, mulmod(z4, sub(add(num15, mul(2, P)), num14), P))
                num0 := add(num0, mulmod(z3, sub(add(num1, mul(3, P)), num0), P))
                num1 := add(num2, mulmod(z3, sub(add(num3, mul(3, P)), num2), P))
                num2 := add(num4, mulmod(z3, sub(add(num5, mul(3, P)), num4), P))
                num3 := add(num6, mulmod(z3, sub(add(num7, mul(3, P)), num6), P))
                num0 := add(num0, mulmod(z2, sub(add(num1, mul(4, P)), num0), P))
                num1 := add(num2, mulmod(z2, sub(add(num3, mul(4, P)), num2), P))
                num1_claim := add(num0, mulmod(z1, sub(add(num1, mul(5, P)), num0), P))
                den0 := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))
                den1 := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))
                den2 := add(den4, mulmod(z4, sub(add(den5, mul(2, P)), den4), P))
                den3 := add(den6, mulmod(z4, sub(add(den7, mul(2, P)), den6), P))
                den4 := add(den8, mulmod(z4, sub(add(den9, mul(2, P)), den8), P))
                den5 := add(den10, mulmod(z4, sub(add(den11, mul(2, P)), den10), P))
                den6 := add(den12, mulmod(z4, sub(add(den13, mul(2, P)), den12), P))
                den7 := add(den14, mulmod(z4, sub(add(den15, mul(2, P)), den14), P))
                den0 := add(den0, mulmod(z3, sub(add(den1, mul(3, P)), den0), P))
                den1 := add(den2, mulmod(z3, sub(add(den3, mul(3, P)), den2), P))
                den2 := add(den4, mulmod(z3, sub(add(den5, mul(3, P)), den4), P))
                den3 := add(den6, mulmod(z3, sub(add(den7, mul(3, P)), den6), P))
                den0 := add(den0, mulmod(z2, sub(add(den1, mul(4, P)), den0), P))
                den1 := add(den2, mulmod(z2, sub(add(den3, mul(4, P)), den2), P))
                den1_claim := add(den0, mulmod(z1, sub(add(den1, mul(5, P)), den0), P))
                if mod(num_acc, P) { revert(0, 0) }
                if iszero(den_acc) { revert(0, 0) }
            }
            // LOGUP2
            let num2_claim
            let den2_claim
            {
                let num_word0 := calldataload(add(ptr, mul(GKR_INIT_POLY_BYTES, 4)))
                let num_word1 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 32)))
                let num_word2 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 64)))
                let num_word3 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 96)))
                let num_word4 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 128)))
                let num_word5 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 160)))
                let num_word6 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 192)))
                let num_word7 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 4), 224)))
                let den_word0 := calldataload(add(ptr, mul(GKR_INIT_POLY_BYTES, 5)))
                let den_word1 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 32)))
                let den_word2 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 64)))
                let den_word3 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 96)))
                let den_word4 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 128)))
                let den_word5 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 160)))
                let den_word6 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 192)))
                let den_word7 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 5), 224)))
                let num0 := shr(128, num_word0)
                let num1 := and(num_word0, MASK)
                let num2 := shr(128, num_word1)
                let num3 := and(num_word1, MASK)
                let num4 := shr(128, num_word2)
                let num5 := and(num_word2, MASK)
                let num6 := shr(128, num_word3)
                let num7 := and(num_word3, MASK)
                let num8 := shr(128, num_word4)
                let num9 := and(num_word4, MASK)
                let num10 := shr(128, num_word5)
                let num11 := and(num_word5, MASK)
                let num12 := shr(128, num_word6)
                let num13 := and(num_word6, MASK)
                let num14 := shr(128, num_word7)
                let num15 := and(num_word7, MASK)
                let den0 := shr(128, den_word0)
                let den1 := and(den_word0, MASK)
                let den2 := shr(128, den_word1)
                let den3 := and(den_word1, MASK)
                let den4 := shr(128, den_word2)
                let den5 := and(den_word2, MASK)
                let den6 := shr(128, den_word3)
                let den7 := and(den_word3, MASK)
                let den8 := shr(128, den_word4)
                let den9 := and(den_word4, MASK)
                let den10 := shr(128, den_word5)
                let den11 := and(den_word5, MASK)
                let den12 := shr(128, den_word6)
                let den13 := and(den_word6, MASK)
                let den14 := shr(128, den_word7)
                let den15 := and(den_word7, MASK)
                let num_acc0 := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                let den_acc0 := mulmod(den0, den1, P)
                let num_acc1 := add(mulmod(num2, den3, P), mulmod(num3, den2, P))
                let den_acc1 := mulmod(den2, den3, P)
                let num_acc2 := add(mulmod(num4, den5, P), mulmod(num5, den4, P))
                let den_acc2 := mulmod(den4, den5, P)
                let num_acc3 := add(mulmod(num6, den7, P), mulmod(num7, den6, P))
                let den_acc3 := mulmod(den6, den7, P)
                let num_acc4 := add(mulmod(num8, den9, P), mulmod(num9, den8, P))
                let den_acc4 := mulmod(den8, den9, P)
                let num_acc5 := add(mulmod(num10, den11, P), mulmod(num11, den10, P))
                let den_acc5 := mulmod(den10, den11, P)
                let num_acc6 := add(mulmod(num12, den13, P), mulmod(num13, den12, P))
                let den_acc6 := mulmod(den12, den13, P)
                let num_acc7 := add(mulmod(num14, den15, P), mulmod(num15, den14, P))
                let den_acc7 := mulmod(den14, den15, P)
                num_acc0 := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                den_acc0 := mulmod(den_acc0, den_acc1, P)
                num_acc1 := add(mulmod(num_acc2, den_acc3, P), mulmod(num_acc3, den_acc2, P))
                den_acc1 := mulmod(den_acc2, den_acc3, P)
                num_acc2 := add(mulmod(num_acc4, den_acc5, P), mulmod(num_acc5, den_acc4, P))
                den_acc2 := mulmod(den_acc4, den_acc5, P)
                num_acc3 := add(mulmod(num_acc6, den_acc7, P), mulmod(num_acc7, den_acc6, P))
                den_acc3 := mulmod(den_acc6, den_acc7, P)
                num_acc0 := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                den_acc0 := mulmod(den_acc0, den_acc1, P)
                num_acc1 := add(mulmod(num_acc2, den_acc3, P), mulmod(num_acc3, den_acc2, P))
                den_acc1 := mulmod(den_acc2, den_acc3, P)
                let num_acc := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                let den_acc := mulmod(den_acc0, den_acc1, P)
                num0 := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                num1 := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                num2 := add(num4, mulmod(z4, sub(add(num5, mul(2, P)), num4), P))
                num3 := add(num6, mulmod(z4, sub(add(num7, mul(2, P)), num6), P))
                num4 := add(num8, mulmod(z4, sub(add(num9, mul(2, P)), num8), P))
                num5 := add(num10, mulmod(z4, sub(add(num11, mul(2, P)), num10), P))
                num6 := add(num12, mulmod(z4, sub(add(num13, mul(2, P)), num12), P))
                num7 := add(num14, mulmod(z4, sub(add(num15, mul(2, P)), num14), P))
                num0 := add(num0, mulmod(z3, sub(add(num1, mul(3, P)), num0), P))
                num1 := add(num2, mulmod(z3, sub(add(num3, mul(3, P)), num2), P))
                num2 := add(num4, mulmod(z3, sub(add(num5, mul(3, P)), num4), P))
                num3 := add(num6, mulmod(z3, sub(add(num7, mul(3, P)), num6), P))
                num0 := add(num0, mulmod(z2, sub(add(num1, mul(4, P)), num0), P))
                num1 := add(num2, mulmod(z2, sub(add(num3, mul(4, P)), num2), P))
                num2_claim := add(num0, mulmod(z1, sub(add(num1, mul(5, P)), num0), P))
                den0 := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))
                den1 := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))
                den2 := add(den4, mulmod(z4, sub(add(den5, mul(2, P)), den4), P))
                den3 := add(den6, mulmod(z4, sub(add(den7, mul(2, P)), den6), P))
                den4 := add(den8, mulmod(z4, sub(add(den9, mul(2, P)), den8), P))
                den5 := add(den10, mulmod(z4, sub(add(den11, mul(2, P)), den10), P))
                den6 := add(den12, mulmod(z4, sub(add(den13, mul(2, P)), den12), P))
                den7 := add(den14, mulmod(z4, sub(add(den15, mul(2, P)), den14), P))
                den0 := add(den0, mulmod(z3, sub(add(den1, mul(3, P)), den0), P))
                den1 := add(den2, mulmod(z3, sub(add(den3, mul(3, P)), den2), P))
                den2 := add(den4, mulmod(z3, sub(add(den5, mul(3, P)), den4), P))
                den3 := add(den6, mulmod(z3, sub(add(den7, mul(3, P)), den6), P))
                den0 := add(den0, mulmod(z2, sub(add(den1, mul(4, P)), den0), P))
                den1 := add(den2, mulmod(z2, sub(add(den3, mul(4, P)), den2), P))
                den2_claim := add(den0, mulmod(z1, sub(add(den1, mul(5, P)), den0), P))
                if mod(num_acc, P) { revert(0, 0) }
                if iszero(den_acc) { revert(0, 0) }
            }
            // LOGUP3
            let num3_claim
            let den3_claim
            {
                let num_word0 := calldataload(add(ptr, mul(GKR_INIT_POLY_BYTES, 6)))
                let num_word1 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 32)))
                let num_word2 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 64)))
                let num_word3 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 96)))
                let num_word4 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 128)))
                let num_word5 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 160)))
                let num_word6 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 192)))
                let num_word7 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 6), 224)))
                let den_word0 := calldataload(add(ptr, mul(GKR_INIT_POLY_BYTES, 7)))
                let den_word1 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 32)))
                let den_word2 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 64)))
                let den_word3 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 96)))
                let den_word4 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 128)))
                let den_word5 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 160)))
                let den_word6 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 192)))
                let den_word7 := calldataload(add(ptr, add(mul(GKR_INIT_POLY_BYTES, 7), 224)))
                let num0 := shr(128, num_word0)
                let num1 := and(num_word0, MASK)
                let num2 := shr(128, num_word1)
                let num3 := and(num_word1, MASK)
                let num4 := shr(128, num_word2)
                let num5 := and(num_word2, MASK)
                let num6 := shr(128, num_word3)
                let num7 := and(num_word3, MASK)
                let num8 := shr(128, num_word4)
                let num9 := and(num_word4, MASK)
                let num10 := shr(128, num_word5)
                let num11 := and(num_word5, MASK)
                let num12 := shr(128, num_word6)
                let num13 := and(num_word6, MASK)
                let num14 := shr(128, num_word7)
                let num15 := and(num_word7, MASK)
                let den0 := shr(128, den_word0)
                let den1 := and(den_word0, MASK)
                let den2 := shr(128, den_word1)
                let den3 := and(den_word1, MASK)
                let den4 := shr(128, den_word2)
                let den5 := and(den_word2, MASK)
                let den6 := shr(128, den_word3)
                let den7 := and(den_word3, MASK)
                let den8 := shr(128, den_word4)
                let den9 := and(den_word4, MASK)
                let den10 := shr(128, den_word5)
                let den11 := and(den_word5, MASK)
                let den12 := shr(128, den_word6)
                let den13 := and(den_word6, MASK)
                let den14 := shr(128, den_word7)
                let den15 := and(den_word7, MASK)
                let num_acc0 := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                let den_acc0 := mulmod(den0, den1, P)
                let num_acc1 := add(mulmod(num2, den3, P), mulmod(num3, den2, P))
                let den_acc1 := mulmod(den2, den3, P)
                let num_acc2 := add(mulmod(num4, den5, P), mulmod(num5, den4, P))
                let den_acc2 := mulmod(den4, den5, P)
                let num_acc3 := add(mulmod(num6, den7, P), mulmod(num7, den6, P))
                let den_acc3 := mulmod(den6, den7, P)
                let num_acc4 := add(mulmod(num8, den9, P), mulmod(num9, den8, P))
                let den_acc4 := mulmod(den8, den9, P)
                let num_acc5 := add(mulmod(num10, den11, P), mulmod(num11, den10, P))
                let den_acc5 := mulmod(den10, den11, P)
                let num_acc6 := add(mulmod(num12, den13, P), mulmod(num13, den12, P))
                let den_acc6 := mulmod(den12, den13, P)
                let num_acc7 := add(mulmod(num14, den15, P), mulmod(num15, den14, P))
                let den_acc7 := mulmod(den14, den15, P)
                num_acc0 := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                den_acc0 := mulmod(den_acc0, den_acc1, P)
                num_acc1 := add(mulmod(num_acc2, den_acc3, P), mulmod(num_acc3, den_acc2, P))
                den_acc1 := mulmod(den_acc2, den_acc3, P)
                num_acc2 := add(mulmod(num_acc4, den_acc5, P), mulmod(num_acc5, den_acc4, P))
                den_acc2 := mulmod(den_acc4, den_acc5, P)
                num_acc3 := add(mulmod(num_acc6, den_acc7, P), mulmod(num_acc7, den_acc6, P))
                den_acc3 := mulmod(den_acc6, den_acc7, P)
                num_acc0 := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                den_acc0 := mulmod(den_acc0, den_acc1, P)
                num_acc1 := add(mulmod(num_acc2, den_acc3, P), mulmod(num_acc3, den_acc2, P))
                den_acc1 := mulmod(den_acc2, den_acc3, P)
                let num_acc := add(mulmod(num_acc0, den_acc1, P), mulmod(num_acc1, den_acc0, P))
                let den_acc := mulmod(den_acc0, den_acc1, P)
                num0 := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                num1 := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                num2 := add(num4, mulmod(z4, sub(add(num5, mul(2, P)), num4), P))
                num3 := add(num6, mulmod(z4, sub(add(num7, mul(2, P)), num6), P))
                num4 := add(num8, mulmod(z4, sub(add(num9, mul(2, P)), num8), P))
                num5 := add(num10, mulmod(z4, sub(add(num11, mul(2, P)), num10), P))
                num6 := add(num12, mulmod(z4, sub(add(num13, mul(2, P)), num12), P))
                num7 := add(num14, mulmod(z4, sub(add(num15, mul(2, P)), num14), P))
                num0 := add(num0, mulmod(z3, sub(add(num1, mul(3, P)), num0), P))
                num1 := add(num2, mulmod(z3, sub(add(num3, mul(3, P)), num2), P))
                num2 := add(num4, mulmod(z3, sub(add(num5, mul(3, P)), num4), P))
                num3 := add(num6, mulmod(z3, sub(add(num7, mul(3, P)), num6), P))
                num0 := add(num0, mulmod(z2, sub(add(num1, mul(4, P)), num0), P))
                num1 := add(num2, mulmod(z2, sub(add(num3, mul(4, P)), num2), P))
                num3_claim := add(num0, mulmod(z1, sub(add(num1, mul(5, P)), num0), P))
                den0 := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))
                den1 := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))
                den2 := add(den4, mulmod(z4, sub(add(den5, mul(2, P)), den4), P))
                den3 := add(den6, mulmod(z4, sub(add(den7, mul(2, P)), den6), P))
                den4 := add(den8, mulmod(z4, sub(add(den9, mul(2, P)), den8), P))
                den5 := add(den10, mulmod(z4, sub(add(den11, mul(2, P)), den10), P))
                den6 := add(den12, mulmod(z4, sub(add(den13, mul(2, P)), den12), P))
                den7 := add(den14, mulmod(z4, sub(add(den15, mul(2, P)), den14), P))
                den0 := add(den0, mulmod(z3, sub(add(den1, mul(3, P)), den0), P))
                den1 := add(den2, mulmod(z3, sub(add(den3, mul(3, P)), den2), P))
                den2 := add(den4, mulmod(z3, sub(add(den5, mul(3, P)), den4), P))
                den3 := add(den6, mulmod(z3, sub(add(den7, mul(3, P)), den6), P))
                den0 := add(den0, mulmod(z2, sub(add(den1, mul(4, P)), den0), P))
                den1 := add(den2, mulmod(z2, sub(add(den3, mul(4, P)), den2), P))
                den3_claim := add(den0, mulmod(z1, sub(add(den1, mul(5, P)), den0), P))
                if mod(num_acc, P) { revert(0, 0) }
                if iszero(den_acc) { revert(0, 0) }
            }
            claim := add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(den3_claim, alpha, P), num3_claim), alpha, P), den2_claim), alpha, P), num2_claim), alpha, P), den1_claim), alpha, P), num1_claim), alpha, P), write_claim), alpha, P), read_claim)
        }
        function acceval_inlinefold_streamrev_evenodd(ptr, z1, z2, z3, z4, alpha) -> claim {
            // strategy 2a: one poly at a time, to encourage streaming
            let num3_acc, num3_claim
            let den3_acc, den3_claim
            {
                // fold 0/1
                let numword0 := calldataload(add(ptr, mul(6, GKR_INIT_POLY_BYTES)))
                let num0 := shr(128, numword0)
                let num1 := and(MASK, numword0)
                let denword0 := calldataload(add(ptr, mul(7, GKR_INIT_POLY_BYTES)))
                let den0 := shr(128, denword0)
                let den1 := and(MASK, denword0)
                num3_acc := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                den3_acc := mulmod(den0, den1, P)
                let numfold0 := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                let denfold0 := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))
                // fold 2/3
                let numword1 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 32)))
                let num2 := shr(128, numword1)
                let num3 := and(MASK, numword1)
                let denword1 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 32)))
                let den2 := shr(128, denword1)
                let den3 := and(MASK, denword1)
                num3_acc := add(mulmod(num3_acc, den2, P), mulmod(den3_acc, num2, P))
                den3_acc := mulmod(den3_acc, den2, P)
                num3_acc := add(mulmod(num3_acc, den3, P), mulmod(den3_acc, num3, P))
                den3_acc := mulmod(den3_acc, den3, P)
                let numfold1 := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                let denfold1 := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))
                // fold 0/1/2/3
                numfold0 := add(numfold0, mulmod(z3, sub(add(numfold1, mul(3, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z3, sub(add(denfold1, mul(3, P)), denfold0), P))

                // fold 4/5
                let numword2 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 64)))
                let num4 := shr(128, numword2)
                let num5 := and(MASK, numword2)
                let denword2 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 64)))
                let den4 := shr(128, denword2)
                let den5 := and(MASK, denword2)
                num3_acc := add(mulmod(num3_acc, den4, P), mulmod(den3_acc, num4, P))
                den3_acc := mulmod(den3_acc, den4, P)
                num3_acc := add(mulmod(num3_acc, den5, P), mulmod(den3_acc, num5, P))
                den3_acc := mulmod(den3_acc, den5, P)
                let numfold2 := add(num4, mulmod(z4, sub(add(num5, mul(2, P)), num4), P))
                let denfold2 := add(den4, mulmod(z4, sub(add(den5, mul(2, P)), den4), P))
                // fold 6/7
                let numword3 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 96)))
                let num6 := shr(128, numword3)
                let num7 := and(MASK, numword3)
                let denword3 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 96)))
                let den6 := shr(128, denword3)
                let den7 := and(MASK, denword3)
                num3_acc := add(mulmod(num3_acc, den6, P), mulmod(den3_acc, num6, P))
                den3_acc := mulmod(den3_acc, den6, P)
                num3_acc := add(mulmod(num3_acc, den7, P), mulmod(den3_acc, num7, P))
                den3_acc := mulmod(den3_acc, den7, P)
                let numfold3 := add(num6, mulmod(z4, sub(add(num7, mul(2, P)), num6), P))
                let denfold3 := add(den6, mulmod(z4, sub(add(den7, mul(2, P)), den6), P))
                // fold 4/5/6/7
                numfold1 := add(numfold2, mulmod(z3, sub(add(numfold3, mul(3, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z3, sub(add(denfold3, mul(3, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))

                // fold 8/9
                let numword4 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 128)))
                let num8 := shr(128, numword4)
                let num9 := and(MASK, numword4)
                let denword4 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 128)))
                let den8 := shr(128, denword4)
                let den9 := and(MASK, denword4)
                num3_acc := add(mulmod(num3_acc, den8, P), mulmod(den3_acc, num8, P))
                den3_acc := mulmod(den3_acc, den8, P)
                num3_acc := add(mulmod(num3_acc, den9, P), mulmod(den3_acc, num9, P))
                den3_acc := mulmod(den3_acc, den9, P)
                let numfold4 := add(num8, mulmod(z4, sub(add(num9, mul(2, P)), num8), P))
                let denfold4 := add(den8, mulmod(z4, sub(add(den9, mul(2, P)), den8), P))
                // fold 10/11
                let numword5 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 160)))
                let num10 := shr(128, numword5)
                let num11 := and(MASK, numword5)
                let denword5 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 160)))
                let den10 := shr(128, denword5)
                let den11 := and(MASK, denword5)
                num3_acc := add(mulmod(num3_acc, den10, P), mulmod(den3_acc, num10, P))
                den3_acc := mulmod(den3_acc, den10, P)
                num3_acc := add(mulmod(num3_acc, den11, P), mulmod(den3_acc, num11, P))
                den3_acc := mulmod(den3_acc, den11, P)
                let numfold5 := add(num10, mulmod(z4, sub(add(num11, mul(2, P)), num10), P))
                let denfold5 := add(den10, mulmod(z4, sub(add(den11, mul(2, P)), den10), P))
                // fold 8/9/10/11
                numfold2 := add(numfold4, mulmod(z3, sub(add(numfold5, mul(3, P)), numfold4), P))
                denfold2 := add(denfold4, mulmod(z3, sub(add(denfold5, mul(3, P)), denfold4), P))

                // fold 12/13
                let numword6 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 192)))
                let num12 := shr(128, numword6)
                let num13 := and(MASK, numword6)
                let denword6 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 192)))
                let den12 := shr(128, denword6)
                let den13 := and(MASK, denword6)
                num3_acc := add(mulmod(num3_acc, den12, P), mulmod(den3_acc, num12, P))
                den3_acc := mulmod(den3_acc, den12, P)
                num3_acc := add(mulmod(num3_acc, den13, P), mulmod(den3_acc, num13, P))
                den3_acc := mulmod(den3_acc, den13, P)
                let numfold6 := add(num12, mulmod(z4, sub(add(num13, mul(2, P)), num12), P))
                let denfold6 := add(den12, mulmod(z4, sub(add(den13, mul(2, P)), den12), P))
                // fold 14/15
                let numword7 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 224)))
                let num14 := shr(128, numword7)
                let num15 := and(MASK, numword7)
                let denword7 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 224)))
                let den14 := shr(128, denword7)
                let den15 := and(MASK, denword7)
                num3_acc := add(mulmod(num3_acc, den14, P), mulmod(den3_acc, num14, P))
                den3_acc := mulmod(den3_acc, den14, P)
                num3_acc := add(mulmod(num3_acc, den15, P), mulmod(den3_acc, num15, P))
                den3_acc := mulmod(den3_acc, den15, P)
                let numfold7 := add(num14, mulmod(z4, sub(add(num15, mul(2, P)), num14), P))
                let denfold7 := add(den14, mulmod(z4, sub(add(den15, mul(2, P)), den14), P))
                // fold 12/13/14/15
                numfold3 := add(numfold6, mulmod(z3, sub(add(numfold7, mul(3, P)), numfold6), P))
                denfold3 := add(denfold6, mulmod(z3, sub(add(denfold7, mul(3, P)), denfold6), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                num3_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                den3_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
            }
            if mod(num3_acc, P) { revert(0, 0) }
            if iszero(den3_acc) { revert(0, 0) }
            {
                let tmp_claim := add(mulmod(den3_claim, alpha, P), num3_claim)
                mstore(GKR_STREAMREV_CLAIM_PTR, tmp_claim)
            }

            let num2_acc, num2_claim
            let den2_acc, den2_claim
            {
                // fold 0/1
                let numword0 := calldataload(add(ptr, mul(4, GKR_INIT_POLY_BYTES)))
                let num0 := shr(128, numword0)
                let num1 := and(MASK, numword0)
                let denword0 := calldataload(add(ptr, mul(5, GKR_INIT_POLY_BYTES)))
                let den0 := shr(128, denword0)
                let den1 := and(MASK, denword0)
                num2_acc := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                den2_acc := mulmod(den0, den1, P)
                let numfold0 := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                let denfold0 := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))
                // fold 2/3
                let numword1 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 32)))
                let num2 := shr(128, numword1)
                let num3 := and(MASK, numword1)
                let denword1 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 32)))
                let den2 := shr(128, denword1)
                let den3 := and(MASK, denword1)
                num2_acc := add(mulmod(num2_acc, den2, P), mulmod(den2_acc, num2, P))
                den2_acc := mulmod(den2_acc, den2, P)
                num2_acc := add(mulmod(num2_acc, den3, P), mulmod(den2_acc, num3, P))
                den2_acc := mulmod(den2_acc, den3, P)
                let numfold1 := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                let denfold1 := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))
                // fold 0/1/2/3
                numfold0 := add(numfold0, mulmod(z3, sub(add(numfold1, mul(3, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z3, sub(add(denfold1, mul(3, P)), denfold0), P))

                // fold 4/5
                let numword2 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 64)))
                let num4 := shr(128, numword2)
                let num5 := and(MASK, numword2)
                let denword2 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 64)))
                let den4 := shr(128, denword2)
                let den5 := and(MASK, denword2)
                num2_acc := add(mulmod(num2_acc, den4, P), mulmod(den2_acc, num4, P))
                den2_acc := mulmod(den2_acc, den4, P)
                num2_acc := add(mulmod(num2_acc, den5, P), mulmod(den2_acc, num5, P))
                den2_acc := mulmod(den2_acc, den5, P)
                let numfold2 := add(num4, mulmod(z4, sub(add(num5, mul(2, P)), num4), P))
                let denfold2 := add(den4, mulmod(z4, sub(add(den5, mul(2, P)), den4), P))
                // fold 6/7
                let numword3 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 96)))
                let num6 := shr(128, numword3)
                let num7 := and(MASK, numword3)
                let denword3 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 96)))
                let den6 := shr(128, denword3)
                let den7 := and(MASK, denword3)
                num2_acc := add(mulmod(num2_acc, den6, P), mulmod(den2_acc, num6, P))
                den2_acc := mulmod(den2_acc, den6, P)
                num2_acc := add(mulmod(num2_acc, den7, P), mulmod(den2_acc, num7, P))
                den2_acc := mulmod(den2_acc, den7, P)
                let numfold3 := add(num6, mulmod(z4, sub(add(num7, mul(2, P)), num6), P))
                let denfold3 := add(den6, mulmod(z4, sub(add(den7, mul(2, P)), den6), P))
                // fold 4/5/6/7
                numfold1 := add(numfold2, mulmod(z3, sub(add(numfold3, mul(3, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z3, sub(add(denfold3, mul(3, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))

                // fold 8/9
                let numword4 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 128)))
                let num8 := shr(128, numword4)
                let num9 := and(MASK, numword4)
                let denword4 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 128)))
                let den8 := shr(128, denword4)
                let den9 := and(MASK, denword4)
                num2_acc := add(mulmod(num2_acc, den8, P), mulmod(den2_acc, num8, P))
                den2_acc := mulmod(den2_acc, den8, P)
                num2_acc := add(mulmod(num2_acc, den9, P), mulmod(den2_acc, num9, P))
                den2_acc := mulmod(den2_acc, den9, P)
                let numfold4 := add(num8, mulmod(z4, sub(add(num9, mul(2, P)), num8), P))
                let denfold4 := add(den8, mulmod(z4, sub(add(den9, mul(2, P)), den8), P))
                // fold 10/11
                let numword5 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 160)))
                let num10 := shr(128, numword5)
                let num11 := and(MASK, numword5)
                let denword5 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 160)))
                let den10 := shr(128, denword5)
                let den11 := and(MASK, denword5)
                num2_acc := add(mulmod(num2_acc, den10, P), mulmod(den2_acc, num10, P))
                den2_acc := mulmod(den2_acc, den10, P)
                num2_acc := add(mulmod(num2_acc, den11, P), mulmod(den2_acc, num11, P))
                den2_acc := mulmod(den2_acc, den11, P)
                let numfold5 := add(num10, mulmod(z4, sub(add(num11, mul(2, P)), num10), P))
                let denfold5 := add(den10, mulmod(z4, sub(add(den11, mul(2, P)), den10), P))
                // fold 8/9/10/11
                numfold2 := add(numfold4, mulmod(z3, sub(add(numfold5, mul(3, P)), numfold4), P))
                denfold2 := add(denfold4, mulmod(z3, sub(add(denfold5, mul(3, P)), denfold4), P))

                // fold 12/13
                let numword6 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 192)))
                let num12 := shr(128, numword6)
                let num13 := and(MASK, numword6)
                let denword6 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 192)))
                let den12 := shr(128, denword6)
                let den13 := and(MASK, denword6)
                num2_acc := add(mulmod(num2_acc, den12, P), mulmod(den2_acc, num12, P))
                den2_acc := mulmod(den2_acc, den12, P)
                num2_acc := add(mulmod(num2_acc, den13, P), mulmod(den2_acc, num13, P))
                den2_acc := mulmod(den2_acc, den13, P)
                let numfold6 := add(num12, mulmod(z4, sub(add(num13, mul(2, P)), num12), P))
                let denfold6 := add(den12, mulmod(z4, sub(add(den13, mul(2, P)), den12), P))
                // fold 14/15
                let numword7 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 224)))
                let num14 := shr(128, numword7)
                let num15 := and(MASK, numword7)
                let denword7 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 224)))
                let den14 := shr(128, denword7)
                let den15 := and(MASK, denword7)
                num2_acc := add(mulmod(num2_acc, den14, P), mulmod(den2_acc, num14, P))
                den2_acc := mulmod(den2_acc, den14, P)
                num2_acc := add(mulmod(num2_acc, den15, P), mulmod(den2_acc, num15, P))
                den2_acc := mulmod(den2_acc, den15, P)
                let numfold7 := add(num14, mulmod(z4, sub(add(num15, mul(2, P)), num14), P))
                let denfold7 := add(den14, mulmod(z4, sub(add(den15, mul(2, P)), den14), P))
                // fold 12/13/14/15
                numfold3 := add(numfold6, mulmod(z3, sub(add(numfold7, mul(3, P)), numfold6), P))
                denfold3 := add(denfold6, mulmod(z3, sub(add(denfold7, mul(3, P)), denfold6), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                num2_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                den2_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
            }
            if mod(num2_acc, P) { revert(0, 0) }
            if iszero(den2_acc) { revert(0, 0) }
            {
                let tmp_claim := mload(GKR_STREAMREV_CLAIM_PTR)
                tmp_claim := add(mulmod(tmp_claim, alpha, P), den2_claim)
                tmp_claim := add(mulmod(tmp_claim, alpha, P), num2_claim)
                mstore(GKR_STREAMREV_CLAIM_PTR, tmp_claim)
            }

            let num1_acc, num1_claim
            let den1_acc, den1_claim
            {
                // fold 0/1
                let numword0 := calldataload(add(ptr, mul(2, GKR_INIT_POLY_BYTES)))
                let num0 := shr(128, numword0)
                let num1 := and(MASK, numword0)
                let denword0 := calldataload(add(ptr, mul(3, GKR_INIT_POLY_BYTES)))
                let den0 := shr(128, denword0)
                let den1 := and(MASK, denword0)
                num1_acc := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                den1_acc := mulmod(den0, den1, P)
                let numfold0 := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                let denfold0 := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))
                // fold 2/3
                let numword1 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 32)))
                let num2 := shr(128, numword1)
                let num3 := and(MASK, numword1)
                let denword1 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 32)))
                let den2 := shr(128, denword1)
                let den3 := and(MASK, denword1)
                num1_acc := add(mulmod(num1_acc, den2, P), mulmod(den1_acc, num2, P))
                den1_acc := mulmod(den1_acc, den2, P)
                num1_acc := add(mulmod(num1_acc, den3, P), mulmod(den1_acc, num3, P))
                den1_acc := mulmod(den1_acc, den3, P)
                let numfold1 := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                let denfold1 := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))
                // fold 0/1/2/3
                numfold0 := add(numfold0, mulmod(z3, sub(add(numfold1, mul(3, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z3, sub(add(denfold1, mul(3, P)), denfold0), P))

                // fold 4/5
                let numword2 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 64)))
                let num4 := shr(128, numword2)
                let num5 := and(MASK, numword2)
                let denword2 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 64)))
                let den4 := shr(128, denword2)
                let den5 := and(MASK, denword2)
                num1_acc := add(mulmod(num1_acc, den4, P), mulmod(den1_acc, num4, P))
                den1_acc := mulmod(den1_acc, den4, P)
                num1_acc := add(mulmod(num1_acc, den5, P), mulmod(den1_acc, num5, P))
                den1_acc := mulmod(den1_acc, den5, P)
                let numfold2 := add(num4, mulmod(z4, sub(add(num5, mul(2, P)), num4), P))
                let denfold2 := add(den4, mulmod(z4, sub(add(den5, mul(2, P)), den4), P))
                // fold 6/7
                let numword3 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 96)))
                let num6 := shr(128, numword3)
                let num7 := and(MASK, numword3)
                let denword3 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 96)))
                let den6 := shr(128, denword3)
                let den7 := and(MASK, denword3)
                num1_acc := add(mulmod(num1_acc, den6, P), mulmod(den1_acc, num6, P))
                den1_acc := mulmod(den1_acc, den6, P)
                num1_acc := add(mulmod(num1_acc, den7, P), mulmod(den1_acc, num7, P))
                den1_acc := mulmod(den1_acc, den7, P)
                let numfold3 := add(num6, mulmod(z4, sub(add(num7, mul(2, P)), num6), P))
                let denfold3 := add(den6, mulmod(z4, sub(add(den7, mul(2, P)), den6), P))
                // fold 4/5/6/7
                numfold1 := add(numfold2, mulmod(z3, sub(add(numfold3, mul(3, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z3, sub(add(denfold3, mul(3, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))

                // fold 8/9
                let numword4 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 128)))
                let num8 := shr(128, numword4)
                let num9 := and(MASK, numword4)
                let denword4 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 128)))
                let den8 := shr(128, denword4)
                let den9 := and(MASK, denword4)
                num1_acc := add(mulmod(num1_acc, den8, P), mulmod(den1_acc, num8, P))
                den1_acc := mulmod(den1_acc, den8, P)
                num1_acc := add(mulmod(num1_acc, den9, P), mulmod(den1_acc, num9, P))
                den1_acc := mulmod(den1_acc, den9, P)
                let numfold4 := add(num8, mulmod(z4, sub(add(num9, mul(2, P)), num8), P))
                let denfold4 := add(den8, mulmod(z4, sub(add(den9, mul(2, P)), den8), P))
                // fold 10/11
                let numword5 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 160)))
                let num10 := shr(128, numword5)
                let num11 := and(MASK, numword5)
                let denword5 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 160)))
                let den10 := shr(128, denword5)
                let den11 := and(MASK, denword5)
                num1_acc := add(mulmod(num1_acc, den10, P), mulmod(den1_acc, num10, P))
                den1_acc := mulmod(den1_acc, den10, P)
                num1_acc := add(mulmod(num1_acc, den11, P), mulmod(den1_acc, num11, P))
                den1_acc := mulmod(den1_acc, den11, P)
                let numfold5 := add(num10, mulmod(z4, sub(add(num11, mul(2, P)), num10), P))
                let denfold5 := add(den10, mulmod(z4, sub(add(den11, mul(2, P)), den10), P))
                // fold 8/9/10/11
                numfold2 := add(numfold4, mulmod(z3, sub(add(numfold5, mul(3, P)), numfold4), P))
                denfold2 := add(denfold4, mulmod(z3, sub(add(denfold5, mul(3, P)), denfold4), P))

                // fold 12/13
                let numword6 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 192)))
                let num12 := shr(128, numword6)
                let num13 := and(MASK, numword6)
                let denword6 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 192)))
                let den12 := shr(128, denword6)
                let den13 := and(MASK, denword6)
                num1_acc := add(mulmod(num1_acc, den12, P), mulmod(den1_acc, num12, P))
                den1_acc := mulmod(den1_acc, den12, P)
                num1_acc := add(mulmod(num1_acc, den13, P), mulmod(den1_acc, num13, P))
                den1_acc := mulmod(den1_acc, den13, P)
                let numfold6 := add(num12, mulmod(z4, sub(add(num13, mul(2, P)), num12), P))
                let denfold6 := add(den12, mulmod(z4, sub(add(den13, mul(2, P)), den12), P))
                // fold 14/15
                let numword7 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 224)))
                let num14 := shr(128, numword7)
                let num15 := and(MASK, numword7)
                let denword7 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 224)))
                let den14 := shr(128, denword7)
                let den15 := and(MASK, denword7)
                num1_acc := add(mulmod(num1_acc, den14, P), mulmod(den1_acc, num14, P))
                den1_acc := mulmod(den1_acc, den14, P)
                num1_acc := add(mulmod(num1_acc, den15, P), mulmod(den1_acc, num15, P))
                den1_acc := mulmod(den1_acc, den15, P)
                let numfold7 := add(num14, mulmod(z4, sub(add(num15, mul(2, P)), num14), P))
                let denfold7 := add(den14, mulmod(z4, sub(add(den15, mul(2, P)), den14), P))
                // fold 12/13/14/15
                numfold3 := add(numfold6, mulmod(z3, sub(add(numfold7, mul(3, P)), numfold6), P))
                denfold3 := add(denfold6, mulmod(z3, sub(add(denfold7, mul(3, P)), denfold6), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                num1_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                den1_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
            }
            if mod(num1_acc, P) { revert(0, 0) }
            if iszero(den1_acc) { revert(0, 0) }
            {
                let tmp_claim := mload(GKR_STREAMREV_CLAIM_PTR)
                tmp_claim := add(mulmod(tmp_claim, alpha, P), den1_claim)
                tmp_claim := add(mulmod(tmp_claim, alpha, P), num1_claim)
                mstore(GKR_STREAMREV_CLAIM_PTR, tmp_claim)
            }

            // WE CONTINUE WITH WRITE
            let write_acc, write_claim
            {
                // fold 0/1
                let word0 := calldataload(add(ptr, GKR_INIT_POLY_BYTES))
                let write0 := shr(128, word0)
                let write1 := and(MASK, word0)
                write_acc := mulmod(write0, write1, P)
                let fold0 := add(write0, mulmod(z4, sub(add(write1, mul(2, P)), write0), P))
                // fold 2/3
                let word1 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 32)))
                let write2 := shr(128, word1)
                let write3 := and(MASK, word1)
                write_acc := mulmod(write_acc, write2, P)
                write_acc := mulmod(write_acc, write3, P)
                let fold1 := add(write2, mulmod(z4, sub(add(write3, mul(2, P)), write2), P))
                // fold 0/1/2/3
                fold0 := add(fold0, mulmod(z3, sub(add(fold1, mul(3, P)), fold0), P))

                // fold 4/5
                let word2 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 64)))
                let write4 := shr(128, word2)
                let write5 := and(MASK, word2)
                write_acc := mulmod(write_acc, write4, P)
                write_acc := mulmod(write_acc, write5, P)
                let fold2 := add(write4, mulmod(z4, sub(add(write5, mul(2, P)), write4), P))
                // fold 6/7
                let word3 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 96)))
                let write6 := shr(128, word3)
                let write7 := and(MASK, word3)
                write_acc := mulmod(write_acc, write6, P)
                write_acc := mulmod(write_acc, write7, P)
                let fold3 := add(write6, mulmod(z4, sub(add(write7, mul(2, P)), write6), P))
                // fold 4/5/6/7
                fold1 := add(fold2, mulmod(z3, sub(add(fold3, mul(3, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7
                fold0 := add(fold0, mulmod(z2, sub(add(fold1, mul(4, P)), fold0), P))

                // fold 8/9
                let word4 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 128)))
                let write8 := shr(128, word4)
                let write9 := and(MASK, word4)
                write_acc := mulmod(write_acc, write8, P)
                write_acc := mulmod(write_acc, write9, P)
                let fold4 := add(write8, mulmod(z4, sub(add(write9, mul(2, P)), write8), P))
                // fold 10/11
                let word5 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 160)))
                let write10 := shr(128, word5)
                let write11 := and(MASK, word5)
                write_acc := mulmod(write_acc, write10, P)
                write_acc := mulmod(write_acc, write11, P)
                let fold5 := add(write10, mulmod(z4, sub(add(write11, mul(2, P)), write10), P))
                // fold 8/9/10/11
                fold2 := add(fold4, mulmod(z3, sub(add(fold5, mul(3, P)), fold4), P))

                // fold 12/13
                let word6 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 192)))
                let write12 := shr(128, word6)
                let write13 := and(MASK, word6)
                write_acc := mulmod(write_acc, write12, P)
                write_acc := mulmod(write_acc, write13, P)
                let fold6 := add(write12, mulmod(z4, sub(add(write13, mul(2, P)), write12), P))
                // fold 14/15
                let word7 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 224)))
                let write14 := shr(128, word7)
                let write15 := and(MASK, word7)
                write_acc := mulmod(write_acc, write14, P)
                write_acc := mulmod(write_acc, write15, P)
                let fold7 := add(write14, mulmod(z4, sub(add(write15, mul(2, P)), write14), P))
                // fold 12/13/14/15
                fold3 := add(fold6, mulmod(z3, sub(add(fold7, mul(3, P)), fold6), P))
                // fold 8/9/10/11/12/13/14/15
                fold1 := add(fold2, mulmod(z2, sub(add(fold3, mul(4, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                write_claim := add(fold0, mulmod(z1, sub(add(fold1, mul(5, P)), fold0), P))
            }
            {
                let tmp_claim := mload(GKR_STREAMREV_CLAIM_PTR)
                tmp_claim := add(mulmod(tmp_claim, alpha, P), write_claim)
                mstore(GKR_STREAMREV_CLAIM_PTR, tmp_claim)
            }

            // WE BEGIN WITH READ
            let read_acc, read_claim
            {
                // fold 0/1
                let word0 := calldataload(ptr)
                let read0 := shr(128, word0)
                let read1 := and(MASK, word0)
                read_acc := mulmod(read0, read1, P)
                let fold0 := add(read0, mulmod(z4, sub(add(read1, mul(2, P)), read0), P))
                // fold 2/3
                let word1 := calldataload(add(ptr, 32))
                let read2 := shr(128, word1)
                let read3 := and(MASK, word1)
                read_acc := mulmod(read_acc, read2, P)
                read_acc := mulmod(read_acc, read3, P)
                let fold1 := add(read2, mulmod(z4, sub(add(read3, mul(2, P)), read2), P))
                // fold 0/1/2/3
                fold0 := add(fold0, mulmod(z3, sub(add(fold1, mul(3, P)), fold0), P))

                // fold 4/5
                let word2 := calldataload(add(ptr, 64))
                let read4 := shr(128, word2)
                let read5 := and(MASK, word2)
                read_acc := mulmod(read_acc, read4, P)
                read_acc := mulmod(read_acc, read5, P)
                let fold2 := add(read4, mulmod(z4, sub(add(read5, mul(2, P)), read4), P))
                // fold 6/7
                let word3 := calldataload(add(ptr, 96))
                let read6 := shr(128, word3)
                let read7 := and(MASK, word3)
                read_acc := mulmod(read_acc, read6, P)
                read_acc := mulmod(read_acc, read7, P)
                let fold3 := add(read6, mulmod(z4, sub(add(read7, mul(2, P)), read6), P))
                // fold 4/5/6/7
                fold1 := add(fold2, mulmod(z3, sub(add(fold3, mul(3, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7
                fold0 := add(fold0, mulmod(z2, sub(add(fold1, mul(4, P)), fold0), P))

                // fold 8/9
                let word4 := calldataload(add(ptr, 128))
                let read8 := shr(128, word4)
                let read9 := and(MASK, word4)
                read_acc := mulmod(read_acc, read8, P)
                read_acc := mulmod(read_acc, read9, P)
                let fold4 := add(read8, mulmod(z4, sub(add(read9, mul(2, P)), read8), P))
                // fold 10/11
                let word5 := calldataload(add(ptr, 160))
                let read10 := shr(128, word5)
                let read11 := and(MASK, word5)
                read_acc := mulmod(read_acc, read10, P)
                read_acc := mulmod(read_acc, read11, P)
                let fold5 := add(read10, mulmod(z4, sub(add(read11, mul(2, P)), read10), P))
                // fold 8/9/10/11
                fold2 := add(fold4, mulmod(z3, sub(add(fold5, mul(3, P)), fold4), P))

                // fold 12/13
                let word6 := calldataload(add(ptr, 192))
                let read12 := shr(128, word6)
                let read13 := and(MASK, word6)
                read_acc := mulmod(read_acc, read12, P)
                read_acc := mulmod(read_acc, read13, P)
                let fold6 := add(read12, mulmod(z4, sub(add(read13, mul(2, P)), read12), P))
                // fold 14/15
                let word7 := calldataload(add(ptr, 224))
                let read14 := shr(128, word7)
                let read15 := and(MASK, word7)
                read_acc := mulmod(read_acc, read14, P)
                read_acc := mulmod(read_acc, read15, P)
                let fold7 := add(read14, mulmod(z4, sub(add(read15, mul(2, P)), read14), P))
                // fold 12/13/14/15
                fold3 := add(fold6, mulmod(z3, sub(add(fold7, mul(3, P)), fold6), P))
                // fold 8/9/10/11/12/13/14/15
                fold1 := add(fold2, mulmod(z2, sub(add(fold3, mul(4, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                read_claim := add(fold0, mulmod(z1, sub(add(fold1, mul(5, P)), fold0), P))
            }
            if iszero(eq(read_acc, write_acc)) { revert(0, 0) }
            {
                let tmp_claim := mload(GKR_STREAMREV_CLAIM_PTR)
                tmp_claim := add(mulmod(tmp_claim, alpha, P), read_claim)
                mstore(GKR_STREAMREV_CLAIM_PTR, tmp_claim)
            }
            claim := mload(GKR_STREAMREV_CLAIM_PTR)
        }

        function acceval_inlinefold_stream_evenodd(ptr, z1, z2, z3, z4, alpha) -> claim {
            // strategy 2a: one poly at a time, to encourage streaming
            // WE BEGIN WITH READ
            let read_acc, read_claim
            {
                // fold 0/1
                let word0 := calldataload(ptr)
                let read0 := shr(128, word0)
                let read1 := and(MASK, word0)
                read_acc := mulmod(read0, read1, P)
                let fold0 := add(read0, mulmod(z4, sub(add(read1, mul(2, P)), read0), P))
                // fold 2/3
                let word1 := calldataload(add(ptr, 32))
                let read2 := shr(128, word1)
                let read3 := and(MASK, word1)
                read_acc := mulmod(read_acc, read2, P)
                read_acc := mulmod(read_acc, read3, P)
                let fold1 := add(read2, mulmod(z4, sub(add(read3, mul(2, P)), read2), P))
                // fold 0/1/2/3
                fold0 := add(fold0, mulmod(z3, sub(add(fold1, mul(3, P)), fold0), P))

                // fold 4/5
                let word2 := calldataload(add(ptr, 64))
                let read4 := shr(128, word2)
                let read5 := and(MASK, word2)
                read_acc := mulmod(read_acc, read4, P)
                read_acc := mulmod(read_acc, read5, P)
                let fold2 := add(read4, mulmod(z4, sub(add(read5, mul(2, P)), read4), P))
                // fold 6/7
                let word3 := calldataload(add(ptr, 96))
                let read6 := shr(128, word3)
                let read7 := and(MASK, word3)
                read_acc := mulmod(read_acc, read6, P)
                read_acc := mulmod(read_acc, read7, P)
                let fold3 := add(read6, mulmod(z4, sub(add(read7, mul(2, P)), read6), P))
                // fold 4/5/6/7
                fold1 := add(fold2, mulmod(z3, sub(add(fold3, mul(3, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7
                fold0 := add(fold0, mulmod(z2, sub(add(fold1, mul(4, P)), fold0), P))

                // fold 8/9
                let word4 := calldataload(add(ptr, 128))
                let read8 := shr(128, word4)
                let read9 := and(MASK, word4)
                read_acc := mulmod(read_acc, read8, P)
                read_acc := mulmod(read_acc, read9, P)
                let fold4 := add(read8, mulmod(z4, sub(add(read9, mul(2, P)), read8), P))
                // fold 10/11
                let word5 := calldataload(add(ptr, 160))
                let read10 := shr(128, word5)
                let read11 := and(MASK, word5)
                read_acc := mulmod(read_acc, read10, P)
                read_acc := mulmod(read_acc, read11, P)
                let fold5 := add(read10, mulmod(z4, sub(add(read11, mul(2, P)), read10), P))
                // fold 8/9/10/11
                fold2 := add(fold4, mulmod(z3, sub(add(fold5, mul(3, P)), fold4), P))

                // fold 12/13
                let word6 := calldataload(add(ptr, 192))
                let read12 := shr(128, word6)
                let read13 := and(MASK, word6)
                read_acc := mulmod(read_acc, read12, P)
                read_acc := mulmod(read_acc, read13, P)
                let fold6 := add(read12, mulmod(z4, sub(add(read13, mul(2, P)), read12), P))
                // fold 14/15
                let word7 := calldataload(add(ptr, 224))
                let read14 := shr(128, word7)
                let read15 := and(MASK, word7)
                read_acc := mulmod(read_acc, read14, P)
                read_acc := mulmod(read_acc, read15, P)
                let fold7 := add(read14, mulmod(z4, sub(add(read15, mul(2, P)), read14), P))
                // fold 12/13/14/15
                fold3 := add(fold6, mulmod(z3, sub(add(fold7, mul(3, P)), fold6), P))
                // fold 8/9/10/11/12/13/14/15
                fold1 := add(fold2, mulmod(z2, sub(add(fold3, mul(4, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                read_claim := add(fold0, mulmod(z1, sub(add(fold1, mul(5, P)), fold0), P))
            }

            // WE CONTINUE WITH WRITE
            let write_acc, write_claim
            {
                // fold 0/1
                let word0 := calldataload(add(ptr, GKR_INIT_POLY_BYTES))
                let write0 := shr(128, word0)
                let write1 := and(MASK, word0)
                write_acc := mulmod(write0, write1, P)
                let fold0 := add(write0, mulmod(z4, sub(add(write1, mul(2, P)), write0), P))
                // fold 2/3
                let word1 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 32)))
                let write2 := shr(128, word1)
                let write3 := and(MASK, word1)
                write_acc := mulmod(write_acc, write2, P)
                write_acc := mulmod(write_acc, write3, P)
                let fold1 := add(write2, mulmod(z4, sub(add(write3, mul(2, P)), write2), P))
                // fold 0/1/2/3
                fold0 := add(fold0, mulmod(z3, sub(add(fold1, mul(3, P)), fold0), P))

                // fold 4/5
                let word2 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 64)))
                let write4 := shr(128, word2)
                let write5 := and(MASK, word2)
                write_acc := mulmod(write_acc, write4, P)
                write_acc := mulmod(write_acc, write5, P)
                let fold2 := add(write4, mulmod(z4, sub(add(write5, mul(2, P)), write4), P))
                // fold 6/7
                let word3 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 96)))
                let write6 := shr(128, word3)
                let write7 := and(MASK, word3)
                write_acc := mulmod(write_acc, write6, P)
                write_acc := mulmod(write_acc, write7, P)
                let fold3 := add(write6, mulmod(z4, sub(add(write7, mul(2, P)), write6), P))
                // fold 4/5/6/7
                fold1 := add(fold2, mulmod(z3, sub(add(fold3, mul(3, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7
                fold0 := add(fold0, mulmod(z2, sub(add(fold1, mul(4, P)), fold0), P))

                // fold 8/9
                let word4 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 128)))
                let write8 := shr(128, word4)
                let write9 := and(MASK, word4)
                write_acc := mulmod(write_acc, write8, P)
                write_acc := mulmod(write_acc, write9, P)
                let fold4 := add(write8, mulmod(z4, sub(add(write9, mul(2, P)), write8), P))
                // fold 10/11
                let word5 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 160)))
                let write10 := shr(128, word5)
                let write11 := and(MASK, word5)
                write_acc := mulmod(write_acc, write10, P)
                write_acc := mulmod(write_acc, write11, P)
                let fold5 := add(write10, mulmod(z4, sub(add(write11, mul(2, P)), write10), P))
                // fold 8/9/10/11
                fold2 := add(fold4, mulmod(z3, sub(add(fold5, mul(3, P)), fold4), P))

                // fold 12/13
                let word6 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 192)))
                let write12 := shr(128, word6)
                let write13 := and(MASK, word6)
                write_acc := mulmod(write_acc, write12, P)
                write_acc := mulmod(write_acc, write13, P)
                let fold6 := add(write12, mulmod(z4, sub(add(write13, mul(2, P)), write12), P))
                // fold 14/15
                let word7 := calldataload(add(ptr, add(GKR_INIT_POLY_BYTES, 224)))
                let write14 := shr(128, word7)
                let write15 := and(MASK, word7)
                write_acc := mulmod(write_acc, write14, P)
                write_acc := mulmod(write_acc, write15, P)
                let fold7 := add(write14, mulmod(z4, sub(add(write15, mul(2, P)), write14), P))
                // fold 12/13/14/15
                fold3 := add(fold6, mulmod(z3, sub(add(fold7, mul(3, P)), fold6), P))
                // fold 8/9/10/11/12/13/14/15
                fold1 := add(fold2, mulmod(z2, sub(add(fold3, mul(4, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                write_claim := add(fold0, mulmod(z1, sub(add(fold1, mul(5, P)), fold0), P))
            }
            if iszero(eq(read_acc, write_acc)) { revert(0, 0) }

            let num1_acc, num1_claim
            let den1_acc, den1_claim
            {
                // fold 0/1
                let numword0 := calldataload(add(ptr, mul(2, GKR_INIT_POLY_BYTES)))
                let num0 := shr(128, numword0)
                let num1 := and(MASK, numword0)
                let denword0 := calldataload(add(ptr, mul(3, GKR_INIT_POLY_BYTES)))
                let den0 := shr(128, denword0)
                let den1 := and(MASK, denword0)
                num1_acc := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                den1_acc := mulmod(den0, den1, P)
                let numfold0 := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                let denfold0 := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))
                // fold 2/3
                let numword1 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 32)))
                let num2 := shr(128, numword1)
                let num3 := and(MASK, numword1)
                let denword1 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 32)))
                let den2 := shr(128, denword1)
                let den3 := and(MASK, denword1)
                num1_acc := add(mulmod(num1_acc, den2, P), mulmod(den1_acc, num2, P))
                den1_acc := mulmod(den1_acc, den2, P)
                num1_acc := add(mulmod(num1_acc, den3, P), mulmod(den1_acc, num3, P))
                den1_acc := mulmod(den1_acc, den3, P)
                let numfold1 := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                let denfold1 := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))
                // fold 0/1/2/3
                numfold0 := add(numfold0, mulmod(z3, sub(add(numfold1, mul(3, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z3, sub(add(denfold1, mul(3, P)), denfold0), P))

                // fold 4/5
                let numword2 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 64)))
                let num4 := shr(128, numword2)
                let num5 := and(MASK, numword2)
                let denword2 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 64)))
                let den4 := shr(128, denword2)
                let den5 := and(MASK, denword2)
                num1_acc := add(mulmod(num1_acc, den4, P), mulmod(den1_acc, num4, P))
                den1_acc := mulmod(den1_acc, den4, P)
                num1_acc := add(mulmod(num1_acc, den5, P), mulmod(den1_acc, num5, P))
                den1_acc := mulmod(den1_acc, den5, P)
                let numfold2 := add(num4, mulmod(z4, sub(add(num5, mul(2, P)), num4), P))
                let denfold2 := add(den4, mulmod(z4, sub(add(den5, mul(2, P)), den4), P))
                // fold 6/7
                let numword3 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 96)))
                let num6 := shr(128, numword3)
                let num7 := and(MASK, numword3)
                let denword3 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 96)))
                let den6 := shr(128, denword3)
                let den7 := and(MASK, denword3)
                num1_acc := add(mulmod(num1_acc, den6, P), mulmod(den1_acc, num6, P))
                den1_acc := mulmod(den1_acc, den6, P)
                num1_acc := add(mulmod(num1_acc, den7, P), mulmod(den1_acc, num7, P))
                den1_acc := mulmod(den1_acc, den7, P)
                let numfold3 := add(num6, mulmod(z4, sub(add(num7, mul(2, P)), num6), P))
                let denfold3 := add(den6, mulmod(z4, sub(add(den7, mul(2, P)), den6), P))
                // fold 4/5/6/7
                numfold1 := add(numfold2, mulmod(z3, sub(add(numfold3, mul(3, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z3, sub(add(denfold3, mul(3, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))

                // fold 8/9
                let numword4 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 128)))
                let num8 := shr(128, numword4)
                let num9 := and(MASK, numword4)
                let denword4 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 128)))
                let den8 := shr(128, denword4)
                let den9 := and(MASK, denword4)
                num1_acc := add(mulmod(num1_acc, den8, P), mulmod(den1_acc, num8, P))
                den1_acc := mulmod(den1_acc, den8, P)
                num1_acc := add(mulmod(num1_acc, den9, P), mulmod(den1_acc, num9, P))
                den1_acc := mulmod(den1_acc, den9, P)
                let numfold4 := add(num8, mulmod(z4, sub(add(num9, mul(2, P)), num8), P))
                let denfold4 := add(den8, mulmod(z4, sub(add(den9, mul(2, P)), den8), P))
                // fold 10/11
                let numword5 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 160)))
                let num10 := shr(128, numword5)
                let num11 := and(MASK, numword5)
                let denword5 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 160)))
                let den10 := shr(128, denword5)
                let den11 := and(MASK, denword5)
                num1_acc := add(mulmod(num1_acc, den10, P), mulmod(den1_acc, num10, P))
                den1_acc := mulmod(den1_acc, den10, P)
                num1_acc := add(mulmod(num1_acc, den11, P), mulmod(den1_acc, num11, P))
                den1_acc := mulmod(den1_acc, den11, P)
                let numfold5 := add(num10, mulmod(z4, sub(add(num11, mul(2, P)), num10), P))
                let denfold5 := add(den10, mulmod(z4, sub(add(den11, mul(2, P)), den10), P))
                // fold 8/9/10/11
                numfold2 := add(numfold4, mulmod(z3, sub(add(numfold5, mul(3, P)), numfold4), P))
                denfold2 := add(denfold4, mulmod(z3, sub(add(denfold5, mul(3, P)), denfold4), P))

                // fold 12/13
                let numword6 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 192)))
                let num12 := shr(128, numword6)
                let num13 := and(MASK, numword6)
                let denword6 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 192)))
                let den12 := shr(128, denword6)
                let den13 := and(MASK, denword6)
                num1_acc := add(mulmod(num1_acc, den12, P), mulmod(den1_acc, num12, P))
                den1_acc := mulmod(den1_acc, den12, P)
                num1_acc := add(mulmod(num1_acc, den13, P), mulmod(den1_acc, num13, P))
                den1_acc := mulmod(den1_acc, den13, P)
                let numfold6 := add(num12, mulmod(z4, sub(add(num13, mul(2, P)), num12), P))
                let denfold6 := add(den12, mulmod(z4, sub(add(den13, mul(2, P)), den12), P))
                // fold 14/15
                let numword7 := calldataload(add(ptr, add(mul(2, GKR_INIT_POLY_BYTES), 224)))
                let num14 := shr(128, numword7)
                let num15 := and(MASK, numword7)
                let denword7 := calldataload(add(ptr, add(mul(3, GKR_INIT_POLY_BYTES), 224)))
                let den14 := shr(128, denword7)
                let den15 := and(MASK, denword7)
                num1_acc := add(mulmod(num1_acc, den14, P), mulmod(den1_acc, num14, P))
                den1_acc := mulmod(den1_acc, den14, P)
                num1_acc := add(mulmod(num1_acc, den15, P), mulmod(den1_acc, num15, P))
                den1_acc := mulmod(den1_acc, den15, P)
                let numfold7 := add(num14, mulmod(z4, sub(add(num15, mul(2, P)), num14), P))
                let denfold7 := add(den14, mulmod(z4, sub(add(den15, mul(2, P)), den14), P))
                // fold 12/13/14/15
                numfold3 := add(numfold6, mulmod(z3, sub(add(numfold7, mul(3, P)), numfold6), P))
                denfold3 := add(denfold6, mulmod(z3, sub(add(denfold7, mul(3, P)), denfold6), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                num1_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                den1_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
            }
            if mod(num1_acc, P) { revert(0, 0) }
            if iszero(den1_acc) { revert(0, 0) }

            let num2_acc, num2_claim
            let den2_acc, den2_claim
            {
                // fold 0/1
                let numword0 := calldataload(add(ptr, mul(4, GKR_INIT_POLY_BYTES)))
                let num0 := shr(128, numword0)
                let num1 := and(MASK, numword0)
                let denword0 := calldataload(add(ptr, mul(5, GKR_INIT_POLY_BYTES)))
                let den0 := shr(128, denword0)
                let den1 := and(MASK, denword0)
                num2_acc := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                den2_acc := mulmod(den0, den1, P)
                let numfold0 := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                let denfold0 := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))
                // fold 2/3
                let numword1 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 32)))
                let num2 := shr(128, numword1)
                let num3 := and(MASK, numword1)
                let denword1 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 32)))
                let den2 := shr(128, denword1)
                let den3 := and(MASK, denword1)
                num2_acc := add(mulmod(num2_acc, den2, P), mulmod(den2_acc, num2, P))
                den2_acc := mulmod(den2_acc, den2, P)
                num2_acc := add(mulmod(num2_acc, den3, P), mulmod(den2_acc, num3, P))
                den2_acc := mulmod(den2_acc, den3, P)
                let numfold1 := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                let denfold1 := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))
                // fold 0/1/2/3
                numfold0 := add(numfold0, mulmod(z3, sub(add(numfold1, mul(3, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z3, sub(add(denfold1, mul(3, P)), denfold0), P))

                // fold 4/5
                let numword2 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 64)))
                let num4 := shr(128, numword2)
                let num5 := and(MASK, numword2)
                let denword2 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 64)))
                let den4 := shr(128, denword2)
                let den5 := and(MASK, denword2)
                num2_acc := add(mulmod(num2_acc, den4, P), mulmod(den2_acc, num4, P))
                den2_acc := mulmod(den2_acc, den4, P)
                num2_acc := add(mulmod(num2_acc, den5, P), mulmod(den2_acc, num5, P))
                den2_acc := mulmod(den2_acc, den5, P)
                let numfold2 := add(num4, mulmod(z4, sub(add(num5, mul(2, P)), num4), P))
                let denfold2 := add(den4, mulmod(z4, sub(add(den5, mul(2, P)), den4), P))
                // fold 6/7
                let numword3 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 96)))
                let num6 := shr(128, numword3)
                let num7 := and(MASK, numword3)
                let denword3 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 96)))
                let den6 := shr(128, denword3)
                let den7 := and(MASK, denword3)
                num2_acc := add(mulmod(num2_acc, den6, P), mulmod(den2_acc, num6, P))
                den2_acc := mulmod(den2_acc, den6, P)
                num2_acc := add(mulmod(num2_acc, den7, P), mulmod(den2_acc, num7, P))
                den2_acc := mulmod(den2_acc, den7, P)
                let numfold3 := add(num6, mulmod(z4, sub(add(num7, mul(2, P)), num6), P))
                let denfold3 := add(den6, mulmod(z4, sub(add(den7, mul(2, P)), den6), P))
                // fold 4/5/6/7
                numfold1 := add(numfold2, mulmod(z3, sub(add(numfold3, mul(3, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z3, sub(add(denfold3, mul(3, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))

                // fold 8/9
                let numword4 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 128)))
                let num8 := shr(128, numword4)
                let num9 := and(MASK, numword4)
                let denword4 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 128)))
                let den8 := shr(128, denword4)
                let den9 := and(MASK, denword4)
                num2_acc := add(mulmod(num2_acc, den8, P), mulmod(den2_acc, num8, P))
                den2_acc := mulmod(den2_acc, den8, P)
                num2_acc := add(mulmod(num2_acc, den9, P), mulmod(den2_acc, num9, P))
                den2_acc := mulmod(den2_acc, den9, P)
                let numfold4 := add(num8, mulmod(z4, sub(add(num9, mul(2, P)), num8), P))
                let denfold4 := add(den8, mulmod(z4, sub(add(den9, mul(2, P)), den8), P))
                // fold 10/11
                let numword5 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 160)))
                let num10 := shr(128, numword5)
                let num11 := and(MASK, numword5)
                let denword5 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 160)))
                let den10 := shr(128, denword5)
                let den11 := and(MASK, denword5)
                num2_acc := add(mulmod(num2_acc, den10, P), mulmod(den2_acc, num10, P))
                den2_acc := mulmod(den2_acc, den10, P)
                num2_acc := add(mulmod(num2_acc, den11, P), mulmod(den2_acc, num11, P))
                den2_acc := mulmod(den2_acc, den11, P)
                let numfold5 := add(num10, mulmod(z4, sub(add(num11, mul(2, P)), num10), P))
                let denfold5 := add(den10, mulmod(z4, sub(add(den11, mul(2, P)), den10), P))
                // fold 8/9/10/11
                numfold2 := add(numfold4, mulmod(z3, sub(add(numfold5, mul(3, P)), numfold4), P))
                denfold2 := add(denfold4, mulmod(z3, sub(add(denfold5, mul(3, P)), denfold4), P))

                // fold 12/13
                let numword6 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 192)))
                let num12 := shr(128, numword6)
                let num13 := and(MASK, numword6)
                let denword6 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 192)))
                let den12 := shr(128, denword6)
                let den13 := and(MASK, denword6)
                num2_acc := add(mulmod(num2_acc, den12, P), mulmod(den2_acc, num12, P))
                den2_acc := mulmod(den2_acc, den12, P)
                num2_acc := add(mulmod(num2_acc, den13, P), mulmod(den2_acc, num13, P))
                den2_acc := mulmod(den2_acc, den13, P)
                let numfold6 := add(num12, mulmod(z4, sub(add(num13, mul(2, P)), num12), P))
                let denfold6 := add(den12, mulmod(z4, sub(add(den13, mul(2, P)), den12), P))
                // fold 14/15
                let numword7 := calldataload(add(ptr, add(mul(4, GKR_INIT_POLY_BYTES), 224)))
                let num14 := shr(128, numword7)
                let num15 := and(MASK, numword7)
                let denword7 := calldataload(add(ptr, add(mul(5, GKR_INIT_POLY_BYTES), 224)))
                let den14 := shr(128, denword7)
                let den15 := and(MASK, denword7)
                num2_acc := add(mulmod(num2_acc, den14, P), mulmod(den2_acc, num14, P))
                den2_acc := mulmod(den2_acc, den14, P)
                num2_acc := add(mulmod(num2_acc, den15, P), mulmod(den2_acc, num15, P))
                den2_acc := mulmod(den2_acc, den15, P)
                let numfold7 := add(num14, mulmod(z4, sub(add(num15, mul(2, P)), num14), P))
                let denfold7 := add(den14, mulmod(z4, sub(add(den15, mul(2, P)), den14), P))
                // fold 12/13/14/15
                numfold3 := add(numfold6, mulmod(z3, sub(add(numfold7, mul(3, P)), numfold6), P))
                denfold3 := add(denfold6, mulmod(z3, sub(add(denfold7, mul(3, P)), denfold6), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                num2_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                den2_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
            }
            if mod(num2_acc, P) { revert(0, 0) }
            if iszero(den2_acc) { revert(0, 0) }

            let num3_acc, num3_claim
            let den3_acc, den3_claim
            {
                // fold 0/1
                let numword0 := calldataload(add(ptr, mul(6, GKR_INIT_POLY_BYTES)))
                let num0 := shr(128, numword0)
                let num1 := and(MASK, numword0)
                let denword0 := calldataload(add(ptr, mul(7, GKR_INIT_POLY_BYTES)))
                let den0 := shr(128, denword0)
                let den1 := and(MASK, denword0)
                num3_acc := add(mulmod(num0, den1, P), mulmod(num1, den0, P))
                den3_acc := mulmod(den0, den1, P)
                let numfold0 := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                let denfold0 := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))
                // fold 2/3
                let numword1 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 32)))
                let num2 := shr(128, numword1)
                let num3 := and(MASK, numword1)
                let denword1 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 32)))
                let den2 := shr(128, denword1)
                let den3 := and(MASK, denword1)
                num3_acc := add(mulmod(num3_acc, den2, P), mulmod(den3_acc, num2, P))
                den3_acc := mulmod(den3_acc, den2, P)
                num3_acc := add(mulmod(num3_acc, den3, P), mulmod(den3_acc, num3, P))
                den3_acc := mulmod(den3_acc, den3, P)
                let numfold1 := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                let denfold1 := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))
                // fold 0/1/2/3
                numfold0 := add(numfold0, mulmod(z3, sub(add(numfold1, mul(3, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z3, sub(add(denfold1, mul(3, P)), denfold0), P))

                // fold 4/5
                let numword2 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 64)))
                let num4 := shr(128, numword2)
                let num5 := and(MASK, numword2)
                let denword2 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 64)))
                let den4 := shr(128, denword2)
                let den5 := and(MASK, denword2)
                num3_acc := add(mulmod(num3_acc, den4, P), mulmod(den3_acc, num4, P))
                den3_acc := mulmod(den3_acc, den4, P)
                num3_acc := add(mulmod(num3_acc, den5, P), mulmod(den3_acc, num5, P))
                den3_acc := mulmod(den3_acc, den5, P)
                let numfold2 := add(num4, mulmod(z4, sub(add(num5, mul(2, P)), num4), P))
                let denfold2 := add(den4, mulmod(z4, sub(add(den5, mul(2, P)), den4), P))
                // fold 6/7
                let numword3 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 96)))
                let num6 := shr(128, numword3)
                let num7 := and(MASK, numword3)
                let denword3 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 96)))
                let den6 := shr(128, denword3)
                let den7 := and(MASK, denword3)
                num3_acc := add(mulmod(num3_acc, den6, P), mulmod(den3_acc, num6, P))
                den3_acc := mulmod(den3_acc, den6, P)
                num3_acc := add(mulmod(num3_acc, den7, P), mulmod(den3_acc, num7, P))
                den3_acc := mulmod(den3_acc, den7, P)
                let numfold3 := add(num6, mulmod(z4, sub(add(num7, mul(2, P)), num6), P))
                let denfold3 := add(den6, mulmod(z4, sub(add(den7, mul(2, P)), den6), P))
                // fold 4/5/6/7
                numfold1 := add(numfold2, mulmod(z3, sub(add(numfold3, mul(3, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z3, sub(add(denfold3, mul(3, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))

                // fold 8/9
                let numword4 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 128)))
                let num8 := shr(128, numword4)
                let num9 := and(MASK, numword4)
                let denword4 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 128)))
                let den8 := shr(128, denword4)
                let den9 := and(MASK, denword4)
                num3_acc := add(mulmod(num3_acc, den8, P), mulmod(den3_acc, num8, P))
                den3_acc := mulmod(den3_acc, den8, P)
                num3_acc := add(mulmod(num3_acc, den9, P), mulmod(den3_acc, num9, P))
                den3_acc := mulmod(den3_acc, den9, P)
                let numfold4 := add(num8, mulmod(z4, sub(add(num9, mul(2, P)), num8), P))
                let denfold4 := add(den8, mulmod(z4, sub(add(den9, mul(2, P)), den8), P))
                // fold 10/11
                let numword5 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 160)))
                let num10 := shr(128, numword5)
                let num11 := and(MASK, numword5)
                let denword5 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 160)))
                let den10 := shr(128, denword5)
                let den11 := and(MASK, denword5)
                num3_acc := add(mulmod(num3_acc, den10, P), mulmod(den3_acc, num10, P))
                den3_acc := mulmod(den3_acc, den10, P)
                num3_acc := add(mulmod(num3_acc, den11, P), mulmod(den3_acc, num11, P))
                den3_acc := mulmod(den3_acc, den11, P)
                let numfold5 := add(num10, mulmod(z4, sub(add(num11, mul(2, P)), num10), P))
                let denfold5 := add(den10, mulmod(z4, sub(add(den11, mul(2, P)), den10), P))
                // fold 8/9/10/11
                numfold2 := add(numfold4, mulmod(z3, sub(add(numfold5, mul(3, P)), numfold4), P))
                denfold2 := add(denfold4, mulmod(z3, sub(add(denfold5, mul(3, P)), denfold4), P))

                // fold 12/13
                let numword6 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 192)))
                let num12 := shr(128, numword6)
                let num13 := and(MASK, numword6)
                let denword6 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 192)))
                let den12 := shr(128, denword6)
                let den13 := and(MASK, denword6)
                num3_acc := add(mulmod(num3_acc, den12, P), mulmod(den3_acc, num12, P))
                den3_acc := mulmod(den3_acc, den12, P)
                num3_acc := add(mulmod(num3_acc, den13, P), mulmod(den3_acc, num13, P))
                den3_acc := mulmod(den3_acc, den13, P)
                let numfold6 := add(num12, mulmod(z4, sub(add(num13, mul(2, P)), num12), P))
                let denfold6 := add(den12, mulmod(z4, sub(add(den13, mul(2, P)), den12), P))
                // fold 14/15
                let numword7 := calldataload(add(ptr, add(mul(6, GKR_INIT_POLY_BYTES), 224)))
                let num14 := shr(128, numword7)
                let num15 := and(MASK, numword7)
                let denword7 := calldataload(add(ptr, add(mul(7, GKR_INIT_POLY_BYTES), 224)))
                let den14 := shr(128, denword7)
                let den15 := and(MASK, denword7)
                num3_acc := add(mulmod(num3_acc, den14, P), mulmod(den3_acc, num14, P))
                den3_acc := mulmod(den3_acc, den14, P)
                num3_acc := add(mulmod(num3_acc, den15, P), mulmod(den3_acc, num15, P))
                den3_acc := mulmod(den3_acc, den15, P)
                let numfold7 := add(num14, mulmod(z4, sub(add(num15, mul(2, P)), num14), P))
                let denfold7 := add(den14, mulmod(z4, sub(add(den15, mul(2, P)), den14), P))
                // fold 12/13/14/15
                numfold3 := add(numfold6, mulmod(z3, sub(add(numfold7, mul(3, P)), numfold6), P))
                denfold3 := add(denfold6, mulmod(z3, sub(add(denfold7, mul(3, P)), denfold6), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                num3_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                den3_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
            }
            if mod(num3_acc, P) { revert(0, 0) }
            if iszero(den3_acc) { revert(0, 0) }
            claim := add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(den3_claim, alpha, P), num3_claim), alpha, P), den2_claim), alpha, P), num2_claim), alpha, P), den1_claim), alpha, P), num1_claim), alpha, P), write_claim), alpha, P), read_claim)
        }

        function acceval_inlinefold_stream_lowhigh(ptr, z1, z2, z3, z4, alpha) -> claim {
            // TODO: fill in the same streaming path with the opposite folding
            // order (low/high first instead of even/odd) for gas golfing.
        }

        function acceval_inlinefold_streamloop_evenodd(ptr, z1, z2, z3, z4, alpha) -> claim {
            // Same current READ+WRITE work as the open-coded even/odd path, but
            // factored into four quarter chunks under a loop.
            let read_acc := 1
            let read_claim
            {
                let fold0, fold1, fold2, fold3
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let base := add(ptr, mul(i, 64))
                    // fold i+0/1
                    let word0 := calldataload(base)
                    let read0 := shr(128, word0)
                    let read1 := and(MASK, word0)
                    read_acc := mulmod(read_acc, read0, P)
                    read_acc := mulmod(read_acc, read1, P)
                    let folda := add(read0, mulmod(z4, sub(add(read1, mul(2, P)), read0), P))
                    // fold i+2/3
                    let word1 := calldataload(add(base, 32))
                    let read2 := shr(128, word1)
                    let read3 := and(MASK, word1)
                    read_acc := mulmod(read_acc, read2, P)
                    read_acc := mulmod(read_acc, read3, P)
                    let foldb := add(read2, mulmod(z4, sub(add(read3, mul(2, P)), read2), P))
                    // fold i+0/1/2/3
                    let foldc := add(folda, mulmod(z3, sub(add(foldb, mul(3, P)), folda), P))
                    switch i
                    case 0 { fold0 := foldc }
                    case 1 { fold1 := foldc }
                    case 2 { fold2 := foldc }
                    default { fold3 := foldc }
                }
                // fold 0/1/2/3/4/5/6/7
                fold0 := add(fold0, mulmod(z2, sub(add(fold1, mul(4, P)), fold0), P))
                // fold 8/9/10/11/12/13/14/15
                fold1 := add(fold2, mulmod(z2, sub(add(fold3, mul(4, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                read_claim := add(fold0, mulmod(z1, sub(add(fold1, mul(5, P)), fold0), P))
            }

            let write_acc := 1
            let write_claim
            {
                let fold0, fold1, fold2, fold3
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let base := add(add(ptr, GKR_INIT_POLY_BYTES), mul(i, 64))
                    // fold i+0/1
                    let word0 := calldataload(base)
                    let write0 := shr(128, word0)
                    let write1 := and(MASK, word0)
                    write_acc := mulmod(write_acc, write0, P)
                    write_acc := mulmod(write_acc, write1, P)
                    let folda := add(write0, mulmod(z4, sub(add(write1, mul(2, P)), write0), P))
                    // fold i+2/3
                    let word1 := calldataload(add(base, 32))
                    let write2 := shr(128, word1)
                    let write3 := and(MASK, word1)
                    write_acc := mulmod(write_acc, write2, P)
                    write_acc := mulmod(write_acc, write3, P)
                    let foldb := add(write2, mulmod(z4, sub(add(write3, mul(2, P)), write2), P))
                    // fold i+0/1/2/3
                    let foldc := add(folda, mulmod(z3, sub(add(foldb, mul(3, P)), folda), P))
                    switch i
                    case 0 { fold0 := foldc }
                    case 1 { fold1 := foldc }
                    case 2 { fold2 := foldc }
                    default { fold3 := foldc }
                }
                // fold 0/1/2/3/4/5/6/7
                fold0 := add(fold0, mulmod(z2, sub(add(fold1, mul(4, P)), fold0), P))
                // fold 8/9/10/11/12/13/14/15
                fold1 := add(fold2, mulmod(z2, sub(add(fold3, mul(4, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                write_claim := add(fold0, mulmod(z1, sub(add(fold1, mul(5, P)), fold0), P))
            }
            if iszero(eq(read_acc, write_acc)) { revert(0, 0) }

            let num1_acc := 0
            let num1_claim
            let den1_acc := 1
            let den1_claim
            {
                let numfold0, numfold1, numfold2, numfold3
                let denfold0, denfold1, denfold2, denfold3
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let numbase := add(add(ptr, mul(2, GKR_INIT_POLY_BYTES)), mul(i, 64))
                    let denbase := add(add(ptr, mul(3, GKR_INIT_POLY_BYTES)), mul(i, 64))

                    // fold i+0/1
                    let numword0 := calldataload(numbase)
                    let num0 := shr(128, numword0)
                    let num1 := and(MASK, numword0)
                    let denword0 := calldataload(denbase)
                    let den0 := shr(128, denword0)
                    let den1 := and(MASK, denword0)
                    num1_acc := add(mulmod(num1_acc, den0, P), mulmod(den1_acc, num0, P))
                    den1_acc := mulmod(den1_acc, den0, P)
                    num1_acc := add(mulmod(num1_acc, den1, P), mulmod(den1_acc, num1, P))
                    den1_acc := mulmod(den1_acc, den1, P)
                    let numfolda := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                    let denfolda := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))

                    // fold i+2/3
                    let numword1 := calldataload(add(numbase, 32))
                    let num2 := shr(128, numword1)
                    let num3 := and(MASK, numword1)
                    let denword1 := calldataload(add(denbase, 32))
                    let den2 := shr(128, denword1)
                    let den3 := and(MASK, denword1)
                    num1_acc := add(mulmod(num1_acc, den2, P), mulmod(den1_acc, num2, P))
                    den1_acc := mulmod(den1_acc, den2, P)
                    num1_acc := add(mulmod(num1_acc, den3, P), mulmod(den1_acc, num3, P))
                    den1_acc := mulmod(den1_acc, den3, P)
                    let numfoldb := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                    let denfoldb := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))

                    // fold i+0/1/2/3
                    let numfoldc := add(numfolda, mulmod(z3, sub(add(numfoldb, mul(3, P)), numfolda), P))
                    let denfoldc := add(denfolda, mulmod(z3, sub(add(denfoldb, mul(3, P)), denfolda), P))
                    switch i
                    case 0 {
                        numfold0 := numfoldc
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
                // fold 0/1/2/3/4/5/6/7
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                num1_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                den1_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
            }
            if mod(num1_acc, P) { revert(0, 0) }
            if iszero(den1_acc) { revert(0, 0) }

            let num2_acc := 0
            let num2_claim
            let den2_acc := 1
            let den2_claim
            {
                let numfold0, numfold1, numfold2, numfold3
                let denfold0, denfold1, denfold2, denfold3
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let numbase := add(add(ptr, mul(4, GKR_INIT_POLY_BYTES)), mul(i, 64))
                    let denbase := add(add(ptr, mul(5, GKR_INIT_POLY_BYTES)), mul(i, 64))

                    // fold i+0/1
                    let numword0 := calldataload(numbase)
                    let num0 := shr(128, numword0)
                    let num1 := and(MASK, numword0)
                    let denword0 := calldataload(denbase)
                    let den0 := shr(128, denword0)
                    let den1 := and(MASK, denword0)
                    num2_acc := add(mulmod(num2_acc, den0, P), mulmod(den2_acc, num0, P))
                    den2_acc := mulmod(den2_acc, den0, P)
                    num2_acc := add(mulmod(num2_acc, den1, P), mulmod(den2_acc, num1, P))
                    den2_acc := mulmod(den2_acc, den1, P)
                    let numfolda := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                    let denfolda := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))

                    // fold i+2/3
                    let numword1 := calldataload(add(numbase, 32))
                    let num2 := shr(128, numword1)
                    let num3 := and(MASK, numword1)
                    let denword1 := calldataload(add(denbase, 32))
                    let den2 := shr(128, denword1)
                    let den3 := and(MASK, denword1)
                    num2_acc := add(mulmod(num2_acc, den2, P), mulmod(den2_acc, num2, P))
                    den2_acc := mulmod(den2_acc, den2, P)
                    num2_acc := add(mulmod(num2_acc, den3, P), mulmod(den2_acc, num3, P))
                    den2_acc := mulmod(den2_acc, den3, P)
                    let numfoldb := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                    let denfoldb := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))

                    // fold i+0/1/2/3
                    let numfoldc := add(numfolda, mulmod(z3, sub(add(numfoldb, mul(3, P)), numfolda), P))
                    let denfoldc := add(denfolda, mulmod(z3, sub(add(denfoldb, mul(3, P)), denfolda), P))
                    switch i
                    case 0 {
                        numfold0 := numfoldc
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
                // fold 0/1/2/3/4/5/6/7
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                num2_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                den2_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
            }
            if mod(num2_acc, P) { revert(0, 0) }
            if iszero(den2_acc) { revert(0, 0) }

            let num3_acc := 0
            let num3_claim
            let den3_acc := 1
            let den3_claim
            {
                let numfold0, numfold1, numfold2, numfold3
                let denfold0, denfold1, denfold2, denfold3
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let numbase := add(add(ptr, mul(6, GKR_INIT_POLY_BYTES)), mul(i, 64))
                    let denbase := add(add(ptr, mul(7, GKR_INIT_POLY_BYTES)), mul(i, 64))

                    // fold i+0/1
                    let numword0 := calldataload(numbase)
                    let num0 := shr(128, numword0)
                    let num1 := and(MASK, numword0)
                    let denword0 := calldataload(denbase)
                    let den0 := shr(128, denword0)
                    let den1 := and(MASK, denword0)
                    num3_acc := add(mulmod(num3_acc, den0, P), mulmod(den3_acc, num0, P))
                    den3_acc := mulmod(den3_acc, den0, P)
                    num3_acc := add(mulmod(num3_acc, den1, P), mulmod(den3_acc, num1, P))
                    den3_acc := mulmod(den3_acc, den1, P)
                    let numfolda := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                    let denfolda := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))

                    // fold i+2/3
                    let numword1 := calldataload(add(numbase, 32))
                    let num2 := shr(128, numword1)
                    let num3 := and(MASK, numword1)
                    let denword1 := calldataload(add(denbase, 32))
                    let den2 := shr(128, denword1)
                    let den3 := and(MASK, denword1)
                    num3_acc := add(mulmod(num3_acc, den2, P), mulmod(den3_acc, num2, P))
                    den3_acc := mulmod(den3_acc, den2, P)
                    num3_acc := add(mulmod(num3_acc, den3, P), mulmod(den3_acc, num3, P))
                    den3_acc := mulmod(den3_acc, den3, P)
                    let numfoldb := add(num2, mulmod(z4, sub(add(num3, mul(2, P)), num2), P))
                    let denfoldb := add(den2, mulmod(z4, sub(add(den3, mul(2, P)), den2), P))

                    // fold i+0/1/2/3
                    let numfoldc := add(numfolda, mulmod(z3, sub(add(numfoldb, mul(3, P)), numfolda), P))
                    let denfoldc := add(denfolda, mulmod(z3, sub(add(denfoldb, mul(3, P)), denfolda), P))
                    switch i
                    case 0 {
                        numfold0 := numfoldc
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
                // fold 0/1/2/3/4/5/6/7
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                num3_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                den3_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
            }
            if mod(num3_acc, P) { revert(0, 0) }
            if iszero(den3_acc) { revert(0, 0) }

            claim := add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(den3_claim, alpha, P), num3_claim), alpha, P), den2_claim), alpha, P), num2_claim), alpha, P), den1_claim), alpha, P), num1_claim), alpha, P), write_claim), alpha, P), read_claim)
        }
        function acceval_inlinefold_streamrevloop_evenodd(ptr, z1, z2, z3, z4, alpha) -> claim {
            // NB: some stack values are explicitly spilled (fold0 and claim updates):
            //     - when written to, it is after stored
            //     - when read, it is first loaded
            // Same current READ+WRITE work as the open-coded even/odd path, but
            // factored into four quarter chunks under a loop.
            let num3_acc := 0
            let num3_claim
            let den3_acc := 1
            let den3_claim
            {
                let numfold0, numfold1, numfold2, numfold3
                let denfold0, denfold1, denfold2, denfold3
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let numbase := add(add(ptr, mul(6, GKR_INIT_POLY_BYTES)), mul(i, 64))
                    let denbase := add(add(ptr, mul(7, GKR_INIT_POLY_BYTES)), mul(i, 64))

                    // fold i+0/1
                    let numword0 := calldataload(numbase)
                    let num0 := shr(128, numword0)
                    let num1 := and(MASK, numword0)
                    let denword0 := calldataload(denbase)
                    let den0 := shr(128, denword0)
                    let den1 := and(MASK, denword0)
                    num3_acc := add(mulmod(num3_acc, den0, P), mulmod(den3_acc, num0, P))
                    den3_acc := mulmod(den3_acc, den0, P)
                    num3_acc := add(mulmod(num3_acc, den1, P), mulmod(den3_acc, num1, P))
                    den3_acc := mulmod(den3_acc, den1, P)
                    let numfolda := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                    let denfolda := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))

                    // fold i+2/3
                    let numword1 := calldataload(add(numbase, 32))
                    let num2 := shr(128, numword1)
                    let num3 := and(MASK, numword1)
                    let denword1 := calldataload(add(denbase, 32))
                    let den2 := shr(128, denword1)
                    let den3 := and(MASK, denword1)
                    num3_acc := add(mulmod(num3_acc, den2, P), mulmod(den3_acc, num2, P))
                    den3_acc := mulmod(den3_acc, den2, P)
                    num3_acc := add(mulmod(num3_acc, den3, P), mulmod(den3_acc, num3, P))
                    den3_acc := mulmod(den3_acc, den3, P)
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
                // fold 0/1/2/3/4/5/6/7
                numfold0 := mload(GKR_INIT_EQ_PTR0)
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                num3_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                den3_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
            }
            if mod(num3_acc, P) { revert(0, 0) }
            if iszero(den3_acc) { revert(0, 0) }
            claim := add(mulmod(den3_claim, alpha, P), num3_claim)
            mstore(CLAIM_PTR, claim)

            let num2_acc := 0
            let num2_claim
            let den2_acc := 1
            let den2_claim
            {
                let numfold0, numfold1, numfold2, numfold3
                let denfold0, denfold1, denfold2, denfold3
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let numbase := add(add(ptr, mul(4, GKR_INIT_POLY_BYTES)), mul(i, 64))
                    let denbase := add(add(ptr, mul(5, GKR_INIT_POLY_BYTES)), mul(i, 64))

                    // fold i+0/1
                    let numword0 := calldataload(numbase)
                    let num0 := shr(128, numword0)
                    let num1 := and(MASK, numword0)
                    let denword0 := calldataload(denbase)
                    let den0 := shr(128, denword0)
                    let den1 := and(MASK, denword0)
                    num2_acc := add(mulmod(num2_acc, den0, P), mulmod(den2_acc, num0, P))
                    den2_acc := mulmod(den2_acc, den0, P)
                    num2_acc := add(mulmod(num2_acc, den1, P), mulmod(den2_acc, num1, P))
                    den2_acc := mulmod(den2_acc, den1, P)
                    let numfolda := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                    let denfolda := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))

                    // fold i+2/3
                    let numword1 := calldataload(add(numbase, 32))
                    let num2 := shr(128, numword1)
                    let num3 := and(MASK, numword1)
                    let denword1 := calldataload(add(denbase, 32))
                    let den2 := shr(128, denword1)
                    let den3 := and(MASK, denword1)
                    num2_acc := add(mulmod(num2_acc, den2, P), mulmod(den2_acc, num2, P))
                    den2_acc := mulmod(den2_acc, den2, P)
                    num2_acc := add(mulmod(num2_acc, den3, P), mulmod(den2_acc, num3, P))
                    den2_acc := mulmod(den2_acc, den3, P)
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
                // fold 0/1/2/3/4/5/6/7
                numfold0 := mload(GKR_INIT_EQ_PTR0)
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                num2_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                den2_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
            }
            if mod(num2_acc, P) { revert(0, 0) }
            if iszero(den2_acc) { revert(0, 0) }
            claim := mload(CLAIM_PTR)
            claim := add(mulmod(claim, alpha, P), den2_claim)
            claim := add(mulmod(claim, alpha, P), num2_claim)
            mstore(CLAIM_PTR, claim)

            let num1_acc := 0
            let num1_claim
            let den1_acc := 1
            let den1_claim
            {
                let numfold0, numfold1, numfold2, numfold3
                let denfold0, denfold1, denfold2, denfold3
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let numbase := add(add(ptr, mul(2, GKR_INIT_POLY_BYTES)), mul(i, 64))
                    let denbase := add(add(ptr, mul(3, GKR_INIT_POLY_BYTES)), mul(i, 64))

                    // fold i+0/1
                    let numword0 := calldataload(numbase)
                    let num0 := shr(128, numword0)
                    let num1 := and(MASK, numword0)
                    let denword0 := calldataload(denbase)
                    let den0 := shr(128, denword0)
                    let den1 := and(MASK, denword0)
                    num1_acc := add(mulmod(num1_acc, den0, P), mulmod(den1_acc, num0, P))
                    den1_acc := mulmod(den1_acc, den0, P)
                    num1_acc := add(mulmod(num1_acc, den1, P), mulmod(den1_acc, num1, P))
                    den1_acc := mulmod(den1_acc, den1, P)
                    let numfolda := add(num0, mulmod(z4, sub(add(num1, mul(2, P)), num0), P))
                    let denfolda := add(den0, mulmod(z4, sub(add(den1, mul(2, P)), den0), P))

                    // fold i+2/3
                    let numword1 := calldataload(add(numbase, 32))
                    let num2 := shr(128, numword1)
                    let num3 := and(MASK, numword1)
                    let denword1 := calldataload(add(denbase, 32))
                    let den2 := shr(128, denword1)
                    let den3 := and(MASK, denword1)
                    num1_acc := add(mulmod(num1_acc, den2, P), mulmod(den1_acc, num2, P))
                    den1_acc := mulmod(den1_acc, den2, P)
                    num1_acc := add(mulmod(num1_acc, den3, P), mulmod(den1_acc, num3, P))
                    den1_acc := mulmod(den1_acc, den3, P)
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
                // fold 0/1/2/3/4/5/6/7
                numfold0 := mload(GKR_INIT_EQ_PTR0)
                numfold0 := add(numfold0, mulmod(z2, sub(add(numfold1, mul(4, P)), numfold0), P))
                denfold0 := add(denfold0, mulmod(z2, sub(add(denfold1, mul(4, P)), denfold0), P))
                // fold 8/9/10/11/12/13/14/15
                numfold1 := add(numfold2, mulmod(z2, sub(add(numfold3, mul(4, P)), numfold2), P))
                denfold1 := add(denfold2, mulmod(z2, sub(add(denfold3, mul(4, P)), denfold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                num1_claim := add(numfold0, mulmod(z1, sub(add(numfold1, mul(5, P)), numfold0), P))
                den1_claim := add(denfold0, mulmod(z1, sub(add(denfold1, mul(5, P)), denfold0), P))
            }
            if mod(num1_acc, P) { revert(0, 0) }
            if iszero(den1_acc) { revert(0, 0) }
            claim := mload(CLAIM_PTR)
            claim := add(mulmod(claim, alpha, P), den1_claim)
            claim := add(mulmod(claim, alpha, P), num1_claim)
            mstore(CLAIM_PTR, claim)

            let write_acc := 1
            let write_claim
            {
                let fold0, fold1, fold2, fold3
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let base := add(add(ptr, GKR_INIT_POLY_BYTES), mul(i, 64))
                    // fold i+0/1
                    let word0 := calldataload(base)
                    let write0 := shr(128, word0)
                    let write1 := and(MASK, word0)
                    write_acc := mulmod(write_acc, write0, P)
                    write_acc := mulmod(write_acc, write1, P)
                    let folda := add(write0, mulmod(z4, sub(add(write1, mul(2, P)), write0), P))
                    // fold i+2/3
                    let word1 := calldataload(add(base, 32))
                    let write2 := shr(128, word1)
                    let write3 := and(MASK, word1)
                    write_acc := mulmod(write_acc, write2, P)
                    write_acc := mulmod(write_acc, write3, P)
                    let foldb := add(write2, mulmod(z4, sub(add(write3, mul(2, P)), write2), P))
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
                // fold 0/1/2/3/4/5/6/7
                fold0 := mload(GKR_INIT_EQ_PTR0)
                fold0 := add(fold0, mulmod(z2, sub(add(fold1, mul(4, P)), fold0), P))
                // fold 8/9/10/11/12/13/14/15
                fold1 := add(fold2, mulmod(z2, sub(add(fold3, mul(4, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                write_claim := add(fold0, mulmod(z1, sub(add(fold1, mul(5, P)), fold0), P))
            }
            claim := mload(CLAIM_PTR)
            claim := add(mulmod(claim, alpha, P), write_claim)
            mstore(CLAIM_PTR, claim)

            let read_acc := 1
            let read_claim
            {
                let fold0, fold1, fold2, fold3
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let base := add(ptr, mul(i, 64))
                    // fold i+0/1
                    let word0 := calldataload(base)
                    let read0 := shr(128, word0)
                    let read1 := and(MASK, word0)
                    read_acc := mulmod(read_acc, read0, P)
                    read_acc := mulmod(read_acc, read1, P)
                    let folda := add(read0, mulmod(z4, sub(add(read1, mul(2, P)), read0), P))
                    // fold i+2/3
                    let word1 := calldataload(add(base, 32))
                    let read2 := shr(128, word1)
                    let read3 := and(MASK, word1)
                    read_acc := mulmod(read_acc, read2, P)
                    read_acc := mulmod(read_acc, read3, P)
                    let foldb := add(read2, mulmod(z4, sub(add(read3, mul(2, P)), read2), P))
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
                // fold 0/1/2/3/4/5/6/7
                fold0 := mload(GKR_INIT_EQ_PTR0)
                fold0 := add(fold0, mulmod(z2, sub(add(fold1, mul(4, P)), fold0), P))
                // fold 8/9/10/11/12/13/14/15
                fold1 := add(fold2, mulmod(z2, sub(add(fold3, mul(4, P)), fold2), P))
                // fold 0/1/2/3/4/5/6/7/8/9/10/11/12/13/14/15
                read_claim := add(fold0, mulmod(z1, sub(add(fold1, mul(5, P)), fold0), P))
            }
            if iszero(eq(read_acc, write_acc)) { revert(0, 0) }
            claim := mload(CLAIM_PTR)
            claim := add(mulmod(claim, alpha, P), read_claim)
        }

        function acceval_inlinefold_streamrevlooploop_evenodd(ptr, z1, z2, z3, z4, alpha) -> claim {
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
            // z1, z2, z3, z4, alpha := transcript128to5_2x64(ptr)
            // z1, z2, z3, z4, alpha := transcript128to5_4x32(ptr)

            // claim := acceval_inlinefold_simple_evenodd(ptr, z1, z2, z3, z4, alpha)
            // claim := acceval_inlinefold_simple_lowhigh(ptr, z1, z2, z3, z4, alpha)
            // claim := acceval_inlinefold_stream_evenodd(ptr, z1, z2, z3, z4, alpha) // VERY BAD
            // claim := acceval_inlinefold_streamrev_evenodd(ptr, z1, z2, z3, z4, alpha) // BAD
            // claim := acceval_inlinefold_streamloop_evenodd(ptr, z1, z2, z3, z4, alpha) // BAD
            // claim := acceval_inlinefold_streamrevloop_evenodd(ptr, z1, z2, z3, z4, alpha)
            // claim := acceval_inlinefold_streamrevlooploop_evenodd(ptr, z1, z2, z3, z4, alpha)
            claim := acceval_inlinefold_streamrevlooploop_evenodd_newunchecked(ptr, z1, z2, z3, z4, alpha)
            // claim := acceval_inlinefold_stream_lowhigh(ptr, z1, z2, z3, z4, alpha)

            next_ptr := add(ptr, GKR_INIT_BYTES)
        }

        function sumcheck_round(ptr, claim) -> next_ptr, next_claim {
            // TODO: the two mods can be batched into one mod + maybe a sub with const*P
            let c0 := shr(128, calldataload(ptr))
            let c1 := shr(128, calldataload(add(ptr, 16)))
            let c2 := shr(128, calldataload(add(ptr, 32)))
            let c3 := shr(128, calldataload(add(ptr, 48)))
            let g0g1 := mod(add(add(add(add(c0, c0), c1), c2), c3), P)
            if iszero(eq(g0g1, claim)) { revert(0, 0) }
            let r := transcript_4to1_single(ptr)
            next_claim := mod(add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0), P)
            next_ptr := add(ptr, 64)
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
            let r := transcript_4to1_dual(w0, w1) // before check is optimal
            if mod(sub(add(claim, mul(6, P)), g0g1), P) { revert(0, 0) }
            // NB: the 17P variant is more gas-efficient
            // but it's risky to use until we have hand measured
            // the max overflow possible in any given circuit
            // for now, i leave it off. feel free to re-enable once measured
            // if mod(sub(add(g0g1, mul(17, P)), claim), P) { revert(0, 0) }
            next_claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
            next_ptr := add(ptr, 64)
        }

        function sumcheck_round_dual_shrshl(ptr, claim) -> next_ptr, next_claim {
            let w0 := calldataload(ptr)
            let w1 := calldataload(add(ptr, 32))
            let c0 := shr(128, w0)
            let c1 := shr(128, shl(128, w0))
            let c2 := shr(128, w1)
            let c3 := shr(128, shl(128, w1))
            let g0g1 := mod(add(add(add(add(c0, c0), c1), c2), c3), P)
            let r := transcript_4to1_dual(w0, w1)
            if iszero(eq(g0g1, claim)) { revert(0, 0) }
            next_claim := mod(add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0), P)
            next_ptr := add(ptr, 64)
        }

        function sumcheck_round_dual_2pass(ptr, claim) -> next_ptr, next_claim {
            let r := 0
            {
                let w0 := calldataload(ptr)
                let w1 := calldataload(add(ptr, 32))
                let c0 := shr(128, w0)
                let c1 := and(w0, MASK)
                let c2 := shr(128, w1)
                let c3 := and(w1, MASK)
                let g0g1 := mod(add(add(add(add(c0, c0), c1), c2), c3), P)
                r := transcript_4to1_dual(w0, w1)
                if iszero(eq(g0g1, claim)) { revert(0, 0) }
            }
            let w0 := calldataload(ptr)
            let w1 := calldataload(add(ptr, 32))
            let c0 := shr(128, w0)
            let c1 := and(w0, MASK)
            let c2 := shr(128, w1)
            let c3 := and(w1, MASK)
            next_claim := mod(add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0), P)
            next_ptr := add(ptr, 64)
        }

        function sumcheck_round_dual_shrshl_2pass(ptr, claim) -> next_ptr, next_claim {
            let r := 0
            {
                let w0 := calldataload(ptr)
                let w1 := calldataload(add(ptr, 32))
                let c0 := shr(128, w0)
                let c1 := shr(128, shl(128, w0))
                let c2 := shr(128, w1)
                let c3 := shr(128, shl(128, w1))
                let g0g1 := mod(add(add(add(add(c0, c0), c1), c2), c3), P)
                r := transcript_4to1_dual(w0, w1)
                if iszero(eq(g0g1, claim)) { revert(0, 0) }
            }
            let w0 := calldataload(ptr)
            let w1 := calldataload(add(ptr, 32))
            let c0 := shr(128, w0)
            let c1 := shr(128, shl(128, w0))
            let c2 := shr(128, w1)
            let c3 := shr(128, shl(128, w1))
            next_claim := mod(add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0), P)
            next_ptr := add(ptr, 64)
        }

        function sumcheck_round_dual_2pass_wbatched(ptr, claim) -> next_ptr, next_claim {
            let w0 := calldataload(ptr)
            let w1 := calldataload(add(ptr, 32))
            let r := 0
            {
                let c0 := shr(128, w0)
                let c1 := and(w0, MASK)
                let c2 := shr(128, w1)
                let c3 := and(w1, MASK)
                let g0g1 := mod(add(add(add(add(c0, c0), c1), c2), c3), P)
                r := transcript_4to1_dual(w0, w1)
                if iszero(eq(g0g1, claim)) { revert(0, 0) }
            }
            let c0 := shr(128, w0)
            let c1 := and(w0, MASK)
            let c2 := shr(128, w1)
            let c3 := and(w1, MASK)
            next_claim := mod(add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0), P)
            next_ptr := add(ptr, 64)
        }

        function sumcheck_round_dual_shrshl_2pass_wbatched(ptr, claim) -> next_ptr, next_claim {
            let w0 := calldataload(ptr)
            let w1 := calldataload(add(ptr, 32))
            let r := 0
            {
                let c0 := shr(128, w0)
                let c1 := shr(128, shl(128, w0))
                let c2 := shr(128, w1)
                let c3 := shr(128, shl(128, w1))
                let g0g1 := mod(add(add(add(add(c0, c0), c1), c2), c3), P)
                r := transcript_4to1_dual(w0, w1)
                if iszero(eq(g0g1, claim)) { revert(0, 0) }
            }
            let c0 := shr(128, w0)
            let c1 := shr(128, shl(128, w0))
            let c2 := shr(128, w1)
            let c3 := shr(128, shl(128, w1))
            next_claim := mod(add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0), P)
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
                let r := transcript_4to1_dual(w0, w1) // before check is optimal
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

        // One x4 side of the unified point check+fold walk: check RLC (alpha)
        // and deferred-fold RLC (next_alpha) over pairs (6,7),(4,5),(2,3) —
        // den then num — then products 1, 0. side_base = ptr for x4 == 0,
        // ptr + 32 for x4 == 1 (every word shifts uniformly). Own frame keeps
        // the limb temps out of the caller's stack budget (solx no-spill).
        // One logup pair on one x4 side (num word at nb, den at nb + 64).
        // Own frame keeps the limb temps off the side-pass loop's budget.
        function compress_pair_side_step(nb, acc, fold, alpha, next_alpha, r_pair) -> nacc, nfold {
            let denword := calldataload(add(nb, GKR_COMPRESSION_POINTCHECK_POLY_BYTES))
            let den0 := shr(128, denword)
            let den1 := and(MASK, denword)
            fold := add(mulmod(fold, next_alpha, P), add(den0, mulmod(r_pair, add(den1, sub(mul(2, P), den0)), P)))
            let numword := calldataload(nb)
            let num0 := shr(128, numword)
            let num1 := and(MASK, numword)
            // den + num check steps combined (den-factored, saves a mulmod):
            // acc*a^2 + a*d0*d1 + n0*d1 + n1*d0 == acc*a^2 + d1*(a*d0 + n0) + n1*d0
            nacc := add(add(mulmod(acc, mulmod(alpha, alpha, P), P), mulmod(den1, add(mulmod(alpha, den0, P), num0), P)), mulmod(num1, den0, P))
            nfold := add(mulmod(fold, next_alpha, P), add(num0, mulmod(r_pair, add(num1, sub(mul(2, P), num0)), P)))
        }

        function compress_side_pass(side_base, alpha, next_alpha, r_pair) -> acc, fold {
            // pair walk by pointer (nb = side_base + 384, 256, 128 == polys 6, 4, 2)
            for { let nb := add(side_base, mul(6, GKR_COMPRESSION_POINTCHECK_POLY_BYTES)) } gt(nb, side_base) { nb := sub(nb, mul(2, GKR_COMPRESSION_POINTCHECK_POLY_BYTES)) } {
                acc, fold := compress_pair_side_step(nb, acc, fold, alpha, next_alpha, r_pair)
            }
            // products by pointer (base = side_base + 64, side_base == polys 1, 0)
            for { let base := add(side_base, GKR_COMPRESSION_POINTCHECK_POLY_BYTES) } iszero(lt(base, side_base)) { base := sub(base, GKR_COMPRESSION_POINTCHECK_POLY_BYTES) } {
                let word := calldataload(base)
                let e0 := shr(128, word)
                let e1 := and(MASK, word)
                acc := add(mulmod(acc, alpha, P), mulmod(e0, e1, P))
                fold := add(mulmod(fold, next_alpha, P), add(e0, mulmod(r_pair, add(e1, sub(mul(2, P), e0)), P)))
            }
        }

        function sumcheck_compress_1pass(ptr, claim, alpha, rounds_skiplast) -> next_ptr, next_claim, next_alpha {
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
                let r := transcript_4to1_dual(w0, w1) // before check is optimal
                // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
                if mod(add(claim, sub(P, g0g1_scaled)), P) { revert(0, 0) }
                claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
                let z := mload(add(POINT_PTR, mul(i, 32)))
                let zr := mulmod(z, r, P)
                eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
                mstore(add(POINT_PTR, mul(i, 32)), r)
                ptr := add(ptr, 64)
            }


            // POINT CHECK+FOLD (unified, strategy A: one walk per x4 side).
            // Draw the fold challenges FIRST — FS-sound: the absorb is a
            // one-shot hash of the whole blob, independent of when we process
            // it (same argument as "draw before check" in the rounds). Then
            // each side's walk computes BOTH the check RLC (alpha) and a
            // deferred-fold RLC (next_alpha). The x4 fold happens once at the
            // end, by linearity:
            //   sum_k a'^k * fold_x4(cl0_k, cl1_k)
            //     = fold_x4(sum_k a'^k * cl0_k, sum_k a'^k * cl1_k)
            // Each calldata word is loaded and limb-split exactly once.
            // TODO: walk may need permuting in the last compression before the
            // circuit (see DIM_REDUCE_INDICES_4 note in the 2pass variant);
            // affects only the check RLC order, not the fold RLC.
            let z_last := mload(add(POINT_PTR, mul(rounds_skiplast, 32)))
            let r_last, r_pair // ie. new (zN, zN+1) points
            r_last, r_pair, next_alpha := transcript32to3(ptr)
            mstore(add(POINT_PTR, mul(rounds_skiplast, 32)), r_last)
            mstore(add(POINT_PTR, mul(add(rounds_skiplast, 1), 32)), r_pair)

            // Both sides run the same walk; x4 = 1 is every address + 32.
            let acc0, fold0
            acc0, fold0 := compress_side_pass(ptr, alpha, next_alpha, r_pair)
            let acc1, fold1
            acc1, fold1 := compress_side_pass(add(ptr, 32), alpha, next_alpha, r_pair)

            // POINT CHECK (z_last captured before the draws overwrote it)
            let diff := add(acc1, sub(mul(2, P), acc0))
            let rhs_scaled := mulmod(add(acc0, mulmod(z_last, diff, P)), eq_scale, P)
            // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
            if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }

            // X4 FOLD (once). fold0/1 < 2^128 + 2P, so pad with 4P.
            next_claim := add(fold0, mulmod(r_last, add(fold1, sub(mul(4, P), fold0)), P))

            next_ptr := add(ptr, GKR_COMPRESSION_POINTCHECK_BYTES)
        }

        // One logup pair (num word at nb, den at nb+64), both x4 sides:
        // updates the check RLCs (alpha) and deferred-fold RLCs (next_alpha).
        // Separate frame keeps the limb temps out of the caller's budget.
        function compress_pair_step(nb, acc0, fold0, acc1, fold1, alpha, next_alpha, r_pair) -> nacc0, nfold0, nacc1, nfold1 {
            {
                let denword := calldataload(add(nb, GKR_COMPRESSION_POINTCHECK_POLY_BYTES))
                let den0 := shr(128, denword)
                let den1 := and(MASK, denword)
                acc0 := add(mulmod(acc0, alpha, P), mulmod(den0, den1, P))
                fold0 := add(mulmod(fold0, next_alpha, P), add(den0, mulmod(r_pair, add(den1, sub(mul(2, P), den0)), P)))
                let numword := calldataload(nb)
                let num0 := shr(128, numword)
                let num1 := and(MASK, numword)
                acc0 := add(mulmod(acc0, alpha, P), add(mulmod(num0, den1, P), mulmod(num1, den0, P)))
                fold0 := add(mulmod(fold0, next_alpha, P), add(num0, mulmod(r_pair, add(num1, sub(mul(2, P), num0)), P)))
            }
            {
                let denword := calldataload(add(nb, add(GKR_COMPRESSION_POINTCHECK_POLY_BYTES, 32)))
                let den0 := shr(128, denword)
                let den1 := and(MASK, denword)
                acc1 := add(mulmod(acc1, alpha, P), mulmod(den0, den1, P))
                fold1 := add(mulmod(fold1, next_alpha, P), add(den0, mulmod(r_pair, add(den1, sub(mul(2, P), den0)), P)))
                let numword := calldataload(add(nb, 32))
                let num0 := shr(128, numword)
                let num1 := and(MASK, numword)
                acc1 := add(mulmod(acc1, alpha, P), add(mulmod(num0, den1, P), mulmod(num1, den0, P)))
                fold1 := add(mulmod(fold1, next_alpha, P), add(num0, mulmod(r_pair, add(num1, sub(mul(2, P), num0)), P)))
            }
            nacc0 := acc0
            nfold0 := fold0
            nacc1 := acc1
            nfold1 := fold1
        }

        function sumcheck_compress_1pass_fused(ptr, claim, alpha, rounds_skiplast) -> next_ptr, next_claim, next_alpha {
            let eq_scale := 1
            for { let i := 0 } lt(i, rounds_skiplast) { i := add(i, 1) } {
                let w0 := calldataload(ptr)
                let w1 := calldataload(add(ptr, 32))
                let c0 := shr(128, w0)
                let c1 := and(w0, MASK)
                let c2 := shr(128, w1)
                let c3 := and(w1, MASK)
                let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P)
                let r := transcript_4to1_dual(w0, w1) // before check is optimal
                if mod(add(claim, sub(P, g0g1_scaled)), P) { revert(0, 0) }
                claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
                let z := mload(add(POINT_PTR, mul(i, 32)))
                let zr := mulmod(z, r, P)
                eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
                mstore(add(POINT_PTR, mul(i, 32)), r)
                ptr := add(ptr, 64)
            }

            // POINT CHECK+FOLD (unified, strategy B: one fused walk, both x4
            // sides per poly). Same math as the 1pass variant; trades the
            // second loop's overhead for higher register pressure (acc0/acc1/
            // fold0/fold1 all live in the loop).
            // z_last read and the new-coord stores are deferred to after the
            // walk (the slot is not overwritten until then) so neither is
            // live inside the fused loop.
            let r_last, r_pair // ie. new (zN, zN+1) points
            r_last, r_pair, next_alpha := transcript32to3(ptr)
            let acc0, fold0, acc1, fold1
            // pair walk by pointer (nb = ptr + 384, 256, 128 == polys 6, 4, 2)
            for { let nb := add(ptr, mul(6, GKR_COMPRESSION_POINTCHECK_POLY_BYTES)) } gt(nb, ptr) { nb := sub(nb, mul(2, GKR_COMPRESSION_POINTCHECK_POLY_BYTES)) } {
                acc0, fold0, acc1, fold1 := compress_pair_step(nb, acc0, fold0, acc1, fold1, alpha, next_alpha, r_pair)
            }
            // products by pointer: base = ptr + 64, ptr == polys 1, 0
            for { let base := add(ptr, GKR_COMPRESSION_POINTCHECK_POLY_BYTES) } iszero(lt(base, ptr)) { base := sub(base, GKR_COMPRESSION_POINTCHECK_POLY_BYTES) } {
                let word := calldataload(base)
                let e0 := shr(128, word)
                let e1 := and(MASK, word)
                acc0 := add(mulmod(acc0, alpha, P), mulmod(e0, e1, P))
                fold0 := add(mulmod(fold0, next_alpha, P), add(e0, mulmod(r_pair, add(e1, sub(mul(2, P), e0)), P)))
                let word1 := calldataload(add(base, 32))
                let e2 := shr(128, word1)
                let e3 := and(MASK, word1)
                acc1 := add(mulmod(acc1, alpha, P), mulmod(e2, e3, P))
                fold1 := add(mulmod(fold1, next_alpha, P), add(e2, mulmod(r_pair, add(e3, sub(mul(2, P), e2)), P)))
            }

            // POINT CHECK, then persist the new coords
            {
                let z_last := mload(add(POINT_PTR, mul(rounds_skiplast, 32)))
                let diff := add(acc1, sub(mul(2, P), acc0))
                let rhs_scaled := mulmod(add(acc0, mulmod(z_last, diff, P)), eq_scale, P)
                if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }
            }
            mstore(add(POINT_PTR, mul(rounds_skiplast, 32)), r_last)
            mstore(add(POINT_PTR, mul(add(rounds_skiplast, 1), 32)), r_pair)

            // X4 FOLD (once). fold0/1 < 2^128 + 2P, so pad with 4P.
            next_claim := add(fold0, mulmod(r_last, add(fold1, sub(mul(4, P), fold0)), P))

            next_ptr := add(ptr, GKR_COMPRESSION_POINTCHECK_BYTES)
        }

        function gkr_compress(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
            for { let layer_vars_skiplast := 3 } lt(layer_vars_skiplast, 23) { layer_vars_skiplast := add(layer_vars_skiplast, 1) } {
                ptr, claim, alpha := sumcheck_compress_1pass(ptr, claim, alpha, layer_vars_skiplast)
            }
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
            // let ptr, claim, alpha := gkr_init_fulleq_u256(0)
            // let ptr, claim, alpha := gkr_init_fulleq_u128(0)
            ptr, claim, alpha := gkr_init_inlinefold(0)
            // mstore(SEED_PTR, GKR_INIT_SEED) // FOR TESTING: post-init FS seed so rounds draw the right r
            // ptr := GKR_INIT_PTR     // FOR TESTING: skip gkr_init, use captured constants
            // alpha := GKR_INIT_ALPHA
            // claim := GKR_INIT_CLAIM
            let init_gas := sub(mload(GKR_INIT_GAS_PTR), gas())
            mstore(GKR_INIT_GAS_PTR, init_gas)
        }

        // MAIN
        {
            mstore(GKR_COMPRESS_GAS_PTR, gas())
            // for { let i := 0 } lt(i, ROUNDS) { i := add(i, 1) } {
            //     // ptr, claim := sumcheck_round(ptr, claim)
            //     ptr, claim := sumcheck_round_dual(ptr, claim)
            //     // ptr, claim := sumcheck_round_dual_shrshl(ptr, claim)
            //     // ptr, claim := sumcheck_round_dual_2pass(ptr, claim)
            //     // ptr, claim := sumcheck_round_dual_shrshl_2pass(ptr, claim)
            //     // ptr, claim := sumcheck_round_dual_2pass_wbatched(ptr, claim)
            //     // ptr, claim := sumcheck_round_dual_shrshl_2pass_wbatched(ptr, claim)
            // }
            ptr, claim, alpha := gkr_compress(ptr, claim, alpha)
            let compress_gas := sub(mload(GKR_COMPRESS_GAS_PTR), gas())
            mstore(GKR_COMPRESS_GAS_PTR, compress_gas)
        }

        // DONE: Proof empty now
        for { let i := 0 } lt(i, 10) { i := add(i, 1) } {
            if calldataload(add(ptr, mul(i, 32))) { revert(0, 0) }
        }

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
contract GKRVerifier2Test is GKRVerifier2 {
    event log_named_uint(string key, uint256 val);
    event log_named_decimal_uint(string key, uint256 val, uint256 decimals);
    event log_named_string(string key, string val);

    function test() external {
        // Generation runs in a separate contract: GKRVerifierTest contains the
        // (memory-unsafe) verifier assembly, which disables the compilers'
        // stack-to-memory spilling for everything compiled into it. Keeping the
        // generator out of this contract means it can grow without ever
        // competing with the verifier for stack budget (solx no-spill etc).
        (bytes memory data, uint256 claim) = (new GKRStreamGen2()).run(ROUNDS);
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
contract GKRStreamGen2 {
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

function generate(uint256) pure returns (bytes memory out, uint256 initial_claim) {
    uint256 p = 0xffffffffffffffffffffffffffffff61;
    uint256 initFieldElements = 8 * 16;
    uint256 initPolySize = 16;
    bytes32 coeff_seed = keccak256("gkr_claude_seed");
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

    bytes32 state = keccak256(abi.encodePacked(bytes32(0), initData));
    uint256 z1 = uint128(uint256(state));
    uint256 z2 = uint256(state) >> 128;

    state = keccak256(abi.encodePacked(state));
    uint256 z3 = uint128(uint256(state));
    uint256 z4 = uint256(state) >> 128;

    state = keccak256(abi.encodePacked(state));
    uint256 alpha = uint128(uint256(state));
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

    out = initData;

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
    //     uint256 r = uint128(uint256(state));
    //
    //     uint256 t = mulmod(uint256(c3), r, p);
    //     t = addmod(t, uint256(c2), p);
    //     t = mulmod(t, r, p);
    //     t = addmod(t, uint256(c1), p);
    //     t = mulmod(t, r, p);
    //     claim = addmod(t, uint256(c0), p);
    // }

    // All 20 compression layers: layer j runs (3 + j) eq-deferred rounds and
    // appends 2 point coords, taking the 8 claims from 2^4-sized polys (after
    // init) up to 2^24-sized polys. claim/alpha come back ready for whatever
    // follows the compression stage.
    for (uint256 layer = 0; layer < 20; ++layer) {
        (out, state, claim, alpha) = generate_compression(
            out, state, claim, alpha, zpoint, keccak256(abi.encodePacked(coeff_seed, layer)), 3 + layer
        );
    }
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
        uint256 r = uint128(uint256(state));

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
    uint256 r_last = uint256(state) & type(uint128).max;
    uint256 r_pair = uint256(state) >> 128;
    state = keccak256(abi.encodePacked(state));
    alpha = uint128(uint256(state));
    zpoint[rounds] = r_last;
    zpoint[rounds + 1] = r_pair;

    // Fold next-layer claims (poly 7 -> 0 Horner, calldata order) so the
    // returned claim/alpha stay correct for chaining more layers.
    claim = fold_pointcheck_claims(evs, r_last, r_pair, alpha);

    return (out, state, claim, alpha);
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
