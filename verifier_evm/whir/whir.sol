// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.24;

// =============================================================================
// WHIR polynomial-commitment opening verifier (EVM skeleton)
// =============================================================================
//
// Hand-written EVM/Yul SKELETON of the WHIR proximity-test verifier, sibling of
// gkr.sol. Realistic gas ESTIMATE, not sound: every equality assert is replaced
// by an anti-DCE sink2(). Stub proof from WhirStreamGen. See whir_schedule.json.
//
// Field: P = 159*2^119 + 1 (~127 bit), one uint128/element, mulmod. keccak256
// for transcript/Merkle/PoW. Mutable state in hand-placed memory "registers"
// (REG_*); heavy logic in shallow Yul fns so the memory-unsafe (non-spilling)
// assembly stays under the EVM stack limit.
//
// ---- Input state: single hashed commitment + calldata preimage --------------
// Instead of ~33 storage slots (seed, batching, opening value, opening point,
// roots), ONE storage slot holds keccak256(preimage). The proof supplies the
// preimage as its first bytes; the verifier hashes it once and checks it against
// the slot (sink). Trades ~33 cold SLOADs (~69k gas) for 1 SLOAD + 1 keccak.
// Preimage layout: [seed:32][batching:16][opening:16][z_initial:nz*16]
//                  [base_cap_0 : CAP*32] ... [base_cap_{nbcaps-1} : CAP*32]
//
// ---- Merkle caps ------------------------------------------------------------
// CAP_LOG2 = log2(cap size). Each commitment is a cap of 2^CAP_LOG2 hashes, so a
// Merkle path is CAP_LOG2 levels shorter. Caps shrink paths (saves
// total_paths*CAP_LOG2 sibling words) but grow every commitment to CAP*32 bytes.
//
// ---- Schedule variants (set VARIANT) ----------------------------------------
//   0=A, 1=B : stock layout, 113 cols over 2^24, k0=1
//   2=PACKED : polys 16x bigger (2^28), 8+1 = 9 batched cols, variable first
//              fold. Search-optimal: folds=[2,4,4,4,5,5] lde2=[4,6,10,13,17,17]
//              q=[13,9,5,4,3,3] pow=30, monomials=2^4.
// =============================================================================

contract WhirVerifier {
    uint256 constant P    = 0x4F80000000000000000000000000000001;
    uint256 constant MASK = 0xffffffffffffffffffffffffffffffff;
    uint256 constant HALF = 0x27C0000000000000000000000000000001;
    uint256 constant GEN     = 5;
    uint256 constant GEN_INV = 0x1FE0000000000000000000000000000001;

    uint256 constant NUM_ROUNDS = 6;
    uint256 constant VARIANT  = 2;  // 0=A, 1=B, 2=PACKED(8col,V=28), 3=FULLYPACKED(1col,V=31)
    uint256 constant MERGED   = 1;  // variants 0/1 only
    // cap size knob: keep CAP == 2^CAP_LOG2 in sync (Yul needs literal constants).
    // 0/1 => single root; 3/8, 4/16, 5/32.
    uint256 constant CAP_LOG2 = 3;
    uint256 constant CAP      = 8;

    // ── hand-placed memory ────────────────────────────────────────────────────
    uint256 constant SINK_PTR     = 64;
    uint256 constant SEED_PTR     = 128;
    uint256 constant Z_PTR        = 2048;
    uint256 constant ACC_PREF_PTR = 2816;
    uint256 constant POW_PTR      = 2880;
    uint256 constant GAMMA_PTR    = 12608;
    uint256 constant FOLD_CH_PTR  = 16256;
    uint256 constant HPO_PTR      = 16448;
    uint256 constant FBUF_PTR     = 16992;
    uint256 constant LEAF_PTR     = 18048;  // leaf hashing + preimage hashing scratch
    uint256 constant REG_CD       = 22400;
    uint256 constant REG_CLAIM    = 22432;
    uint256 constant REG_NUMPOW   = 22464;
    uint256 constant REG_ZIOFF    = 22496;
    uint256 constant REG_CC       = 22560;
    uint256 constant REG_CURDELIN = 22592;
    uint256 constant MONO_PTR     = 22752;  // final monomials (<=16*32)
    // cap regions (each holds up to CAP*32 = 1024 bytes at CAP=32)
    uint256 constant BCAP0_PTR    = 23296;  // base oracle caps
    uint256 constant BCAP1_PTR    = 24320;
    uint256 constant BCAP2_PTR    = 25344;
    uint256 constant QCAP_PTR     = 26368;  // current query cap (rounds >= 1)
    uint256 constant NCAP_PTR     = 27392;  // just-read intermediate cap

    fallback() external {
        assembly {
        function sink2(a, b) { mstore(SINK_PTR, xor(mload(SINK_PTR), xor(a, b))) }
        function draw1() -> r {
            let s := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, s)
            r := shr(128, s)
        }
        function powmod(base, e) -> res {
            res := 1
            base := mod(base, P)
            for {} e { e := shr(1, e) } {
                if and(e, 1) { res := mulmod(res, base, P) }
                base := mulmod(base, base, P)
            }
        }
        function exp_pow2(x, k) -> res {
            res := x
            for { let i := 0 } lt(i, k) { i := add(i, 1) } { res := mulmod(res, res, P) }
        }
        function verify_pow(cp, pow_bits) -> next_cd {
            let nonce := shr(192, calldataload(cp))
            mstore(add(SEED_PTR, 32), shl(192, nonce))
            let h := keccak256(SEED_PTR, 40)
            mstore(SEED_PTR, h)
            sink2(shr(sub(256, pow_bits), h), 0)
            next_cd := add(cp, 8)
        }
        function fold_accumulator(alpha, n, zi_off) {
            let one_minus_alpha := addmod(1, sub(P, alpha), P)
            let alpha_coeff := addmod(addmod(alpha, alpha, P), sub(P, 1), P)
            let zi := mload(add(Z_PTR, zi_off))
            let eqv := addmod(one_minus_alpha, mulmod(alpha_coeff, zi, P), P)
            mstore(ACC_PREF_PTR, mulmod(mload(ACC_PREF_PTR), eqv, P))
            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                let b := add(POW_PTR, mul(i, 96))
                let s := mload(b)
                eqv := addmod(one_minus_alpha, mulmod(alpha_coeff, s, P), P)
                mstore(add(b, 32), mulmod(mload(add(b, 32)), eqv, P))
                mstore(b, mulmod(s, s, P))
            }
        }
        function compute_hpo(fold) {
            let count := shl(sub(fold, 1), 1)
            mstore(HPO_PTR, 1)
            let pw := GEN_INV
            for { let i := 1 } lt(i, count) { i := add(i, 1) } {
                mstore(add(HPO_PTR, mul(i, 32)), pw)
                pw := mulmod(pw, GEN_INV, P)
            }
        }
        function fold_coset(fold, base_root_inv) -> folded {
            let n := shl(fold, 1)
            let root_inv := base_root_inv
            for { let round := 0 } lt(round, fold) { round := add(round, 1) } {
                let half := shr(1, n)
                let ch := mload(add(FOLD_CH_PTR, mul(round, 32)))
                for { let i := 0 } lt(i, half) { i := add(i, 1) } {
                    let a := mload(add(FBUF_PTR, mul(mul(i, 2), 32)))
                    let b := mload(add(FBUF_PTR, mul(add(mul(i, 2), 1), 32)))
                    let t := mulmod(addmod(a, sub(P, b), P), ch, P)
                    let root := mulmod(root_inv, mload(add(HPO_PTR, mul(i, 32))), P)
                    t := mulmod(t, root, P)
                    t := addmod(addmod(t, a, P), b, P)
                    t := mulmod(t, HALF, P)
                    mstore(add(FBUF_PTR, mul(i, 32)), t)
                }
                root_inv := mulmod(root_inv, root_inv, P)
                n := half
            }
            folded := mload(FBUF_PTR)
        }
        // Merkle path of `depth` levels (already cap-reduced), then match a cap
        // entry. depth = query_index_bits - CAP_LOG2.
        function merkle_path(leaf_hash, depth, cap_ptr, cp) -> next_cd {
            let h := leaf_hash
            for { let lvl := 0 } lt(lvl, depth) { lvl := add(lvl, 1) } {
                mstore(0, h)
                mstore(32, calldataload(cp))
                h := keccak256(0, 64)
                cp := add(cp, 32)
            }
            sink2(h, mload(cap_ptr)) // real: match h against cap[top bits of index]
            next_cd := cp
        }
        function batch_oracle(cp, cols, goff, vp, depth, cap_ptr) -> next_cd {
            let wpc := shr(1, vp)
            let li := 0
            for { let c := 0 } lt(c, cols) { c := add(c, 1) } {
                let gamma := mload(add(GAMMA_PTR, mul(add(goff, c), 32)))
                for { let wj := 0 } lt(wj, wpc) { wj := add(wj, 1) } {
                    let w := calldataload(cp)
                    cp := add(cp, 32)
                    mstore(add(LEAF_PTR, mul(li, 32)), w)
                    li := add(li, 1)
                    let s0 := add(FBUF_PTR, mul(mul(wj, 2), 32))
                    let s1 := add(FBUF_PTR, mul(add(mul(wj, 2), 1), 32))
                    mstore(s0, addmod(mload(s0), mulmod(gamma, shr(128, w), P), P))
                    mstore(s1, addmod(mload(s1), mulmod(gamma, and(w, MASK), P), P))
                }
            }
            next_cd := merkle_path(keccak256(LEAF_PTR, mul(li, 32)), depth, cap_ptr, cp)
        }
        function read_leaf(cp, vp, depth, cap_ptr) -> next_cd {
            let words := shr(1, vp)
            for { let i := 0 } lt(i, words) { i := add(i, 1) } {
                let w := calldataload(cp)
                mstore(add(LEAF_PTR, mul(i, 32)), w)
                mstore(add(FBUF_PTR, mul(mul(i, 2), 32)), shr(128, w))
                mstore(add(FBUF_PTR, mul(add(mul(i, 2), 1), 32)), and(w, MASK))
                cp := add(cp, 32)
            }
            next_cd := merkle_path(keccak256(LEAF_PTR, mul(words, 32)), depth, cap_ptr, cp)
        }
        function push_pow(current_scalar, coefficient) {
            let n := mload(REG_NUMPOW)
            let b := add(POW_PTR, mul(n, 96))
            mstore(b, current_scalar)
            mstore(add(b, 32), 1)
            mstore(add(b, 64), coefficient)
            mstore(REG_NUMPOW, add(n, 1))
        }
        function copy_cap(dst, src) {
            for { let i := 0 } lt(i, CAP) { i := add(i, 1) } {
                mstore(add(dst, mul(i, 32)), mload(add(src, mul(i, 32))))
            }
        }

        function do_query(r, fold, qib, vp, idx_mask, delin) {
            let cp := mload(REG_CD)
            let cur := mulmod(mload(REG_CURDELIN), delin, P)
            mstore(REG_CURDELIN, cur)
            let qidx := and(draw1(), idx_mask)
            let base_root_inv := powmod(GEN_INV, qidx)
            let depth := sub(qib, CAP_LOG2)

            switch r
            case 0 {
                switch VARIANT
                case 3 {
                    // FULLYPACKED: round 0 is a single pre-batched column / one tree
                    cp := read_leaf(cp, vp, depth, BCAP0_PTR)
                }
                case 2 {
                    for { let j := 0 } lt(j, vp) { j := add(j, 1) } { mstore(add(FBUF_PTR, mul(j, 32)), 0) }
                    cp := batch_oracle(cp, 8, 0, vp, depth, BCAP0_PTR)
                    cp := batch_oracle(cp, 1, 8, vp, depth, BCAP1_PTR)
                }
                default {
                    for { let j := 0 } lt(j, vp) { j := add(j, 1) } { mstore(add(FBUF_PTR, mul(j, 32)), 0) }
                    switch MERGED
                    case 1 {
                        cp := batch_oracle(cp, 103, 0,   vp, depth, BCAP0_PTR)
                        cp := batch_oracle(cp, 10,  103, vp, depth, BCAP1_PTR)
                    }
                    default {
                        cp := batch_oracle(cp, 38, 0,   vp, depth, BCAP0_PTR)
                        cp := batch_oracle(cp, 65, 38,  vp, depth, BCAP1_PTR)
                        cp := batch_oracle(cp, 10, 103, vp, depth, BCAP2_PTR)
                    }
                }
            }
            default {
                cp := read_leaf(cp, vp, depth, QCAP_PTR)
            }
            mstore(REG_CD, cp)
            let folded := fold_coset(fold, base_root_inv)
            push_pow(exp_pow2(powmod(GEN, qidx), fold), cur)
            mstore(REG_CC, addmod(mload(REG_CC), mulmod(folded, cur, P), P))
        }

        function do_internal(r, fold, q, pow_bits, qib, vp, idx_mask) {
            let cp := mload(REG_CD)
            // read + absorb the next oracle's CAP (CAP*32 bytes)
            calldatacopy(NCAP_PTR, cp, mul(CAP, 32))
            calldatacopy(add(SEED_PTR, 32), cp, mul(CAP, 32))
            mstore(SEED_PTR, keccak256(SEED_PTR, add(32, mul(CAP, 32))))
            cp := add(cp, mul(CAP, 32))
            let ood_point := draw1()
            let ood_value := shr(128, calldataload(cp))
            calldatacopy(add(SEED_PTR, 32), cp, 16)
            mstore(SEED_PTR, keccak256(SEED_PTR, 48))
            cp := add(cp, 16)
            cp := verify_pow(cp, pow_bits)
            let delin := draw1()
            mstore(REG_CD, cp)
            push_pow(ood_point, delin)
            mstore(REG_CC, mulmod(ood_value, delin, P))
            mstore(REG_CURDELIN, delin)
            compute_hpo(fold)
            for { let qq := 0 } lt(qq, q) { qq := add(qq, 1) } {
                do_query(r, fold, qib, vp, idx_mask, delin)
            }
            mstore(REG_CLAIM, addmod(mload(REG_CLAIM), mload(REG_CC), P))
            copy_cap(QCAP_PTR, NCAP_PTR) // this round's intermediate cap is next round's query cap
        }

        function do_final(fold, q, pow_bits, qib, vp, idx_mask, zi_off, rfin) {
            let nmono := shl(rfin, 1)
            let cp := mload(REG_CD)
            calldatacopy(add(SEED_PTR, 32), cp, mul(nmono, 16))
            mstore(SEED_PTR, keccak256(SEED_PTR, add(32, mul(nmono, 16))))
            for { let wj := 0 } lt(wj, shr(1, nmono)) { wj := add(wj, 1) } {
                let w := calldataload(add(cp, mul(wj, 32)))
                mstore(add(MONO_PTR, mul(mul(wj, 2), 32)), shr(128, w))
                mstore(add(MONO_PTR, mul(add(mul(wj, 2), 1), 32)), and(w, MASK))
            }
            cp := add(cp, mul(nmono, 16))
            cp := verify_pow(cp, pow_bits)
            compute_hpo(fold)
            let depth := sub(qib, CAP_LOG2)

            for { let qq := 0 } lt(qq, q) { qq := add(qq, 1) } {
                let qidx := and(draw1(), idx_mask)
                let base_root := powmod(GEN, qidx)
                cp := read_leaf(cp, vp, depth, QCAP_PTR)
                let folded := fold_coset(fold, powmod(GEN_INV, qidx))
                let qp := exp_pow2(base_root, fold)
                let ev := mload(add(MONO_PTR, mul(sub(nmono, 1), 32)))
                for { let j := sub(nmono, 1) } gt(j, 0) { j := sub(j, 1) } {
                    ev := addmod(mulmod(ev, qp, P), mload(add(MONO_PTR, mul(sub(j, 1), 32))), P)
                }
                sink2(ev, folded)
            }
            mstore(REG_CD, cp)

            for { let i := 0 } lt(i, nmono) { i := add(i, 1) } {
                mstore(add(FBUF_PTR, mul(i, 32)), mload(add(MONO_PTR, mul(i, 32))))
            }
            let active := nmono
            for { let level := 0 } lt(level, rfin) { level := add(level, 1) } {
                let half := shr(1, active)
                let zj := mload(add(Z_PTR, add(zi_off, mul(level, 32))))
                for { let i := 0 } lt(i, half) { i := add(i, 1) } {
                    let c0 := mload(add(FBUF_PTR, mul(mul(i, 2), 32)))
                    let c1 := mload(add(FBUF_PTR, mul(add(mul(i, 2), 1), 32)))
                    mstore(add(FBUF_PTR, mul(i, 32)), addmod(c0, mulmod(c1, zj, P), P))
                }
                active := half
            }
            let expected := mulmod(mload(ACC_PREF_PTR), mload(FBUF_PTR), P)
            let n := mload(REG_NUMPOW)
            for { let e := 0 } lt(e, n) { e := add(e, 1) } {
                let b := add(POW_PTR, mul(e, 96))
                let s := mload(b)
                let ev := mload(add(MONO_PTR, mul(sub(nmono, 1), 32)))
                for { let j := sub(nmono, 1) } gt(j, 0) { j := sub(j, 1) } {
                    ev := addmod(mulmod(ev, s, P), mload(add(MONO_PTR, mul(sub(j, 1), 32))), P)
                }
                ev := mulmod(ev, mload(add(b, 32)), P)
                ev := mulmod(ev, mload(add(b, 64)), P)
                expected := addmod(expected, ev, P)
            }
            sink2(expected, mload(REG_CLAIM))
        }

        // =================================================================== MAIN
        let start_gas := gas()

        let nz := 24
        let gcount := 113
        let rfin := 1
        let nbcaps := 2
        if eq(VARIANT, 2) { nz := 28 gcount := 9 rfin := 4 }
        // FULLYPACKED: 113 polys -> ONE poly of 2^(24+ceil(log2 113)) = 2^31, 1 column, 1 tree
        if eq(VARIANT, 3) { nz := 31 gcount := 1 rfin := 4 nbcaps := 1 }
        if and(lt(VARIANT, 2), iszero(MERGED)) { nbcaps := 3 }

        // ---- parse + verify the single hashed state commitment -------------
        // preimage at calldata [0, plen): seed | batching | opening | z | base caps
        mstore(SEED_PTR, calldataload(0))
        let w1 := calldataload(32)
        let batching := shr(128, w1)
        mstore(REG_CLAIM, and(w1, MASK)) // opening value
        // z_initial (nz elems, packed 2/word; nz may be odd) at offset 64
        let zwords := shr(1, add(nz, 1)) // ceil(nz/2)
        for { let i := 0 } lt(i, zwords) { i := add(i, 1) } {
            let w := calldataload(add(64, mul(i, 32)))
            mstore(add(Z_PTR, mul(mul(i, 2), 32)), shr(128, w))
            mstore(add(Z_PTR, mul(add(mul(i, 2), 1), 32)), and(w, MASK))
        }
        // base caps
        let caps_off := add(64, mul(zwords, 32))
        calldatacopy(BCAP0_PTR, caps_off, mul(CAP, 32))
        calldatacopy(BCAP1_PTR, add(caps_off, mul(CAP, 32)), mul(CAP, 32))
        if eq(nbcaps, 3) { calldatacopy(BCAP2_PTR, add(caps_off, mul(2, mul(CAP, 32))), mul(CAP, 32)) }
        let plen := add(caps_off, mul(nbcaps, mul(CAP, 32)))
        // hash preimage, check vs the single stored commitment (sink)
        calldatacopy(LEAF_PTR, 0, plen)
        sink2(keccak256(LEAF_PTR, plen), sload(0))

        // gamma powers
        mstore(GAMMA_PTR, 1)
        {
            let g := 1
            for { let i := 1 } lt(i, gcount) { i := add(i, 1) } {
                g := mulmod(g, batching, P)
                mstore(add(GAMMA_PTR, mul(i, 32)), g)
            }
        }

        mstore(ACC_PREF_PTR, 1)
        mstore(REG_NUMPOW, 0)
        mstore(REG_ZIOFF, 0)
        mstore(REG_CD, plen) // proof stream starts after the preimage

        for { let r := 0 } lt(r, NUM_ROUNDS) { r := add(r, 1) } {
            let fold, q, pow_bits, qib, vp
            switch VARIANT
            case 0 {
                switch r
                case 0 { fold := 1 q := 13 pow_bits := 30 qib := 27 vp := 2 }
                case 1 { fold := 5 q := 10 pow_bits := 30 qib := 23 vp := 32 }
                case 2 { fold := 5 q := 5  pow_bits := 30 qib := 23 vp := 32 }
                case 3 { fold := 5 q := 4  pow_bits := 20 qib := 23 vp := 32 }
                case 4 { fold := 4 q := 3  pow_bits := 20 qib := 24 vp := 16 }
                default { fold := 3 q := 2 pow_bits := 32 qib := 25 vp := 8 }
            }
            case 1 {
                switch r
                case 0 { fold := 1 q := 10 pow_bits := 30 qib := 28 vp := 2 }
                case 1 { fold := 5 q := 8  pow_bits := 32 qib := 24 vp := 32 }
                case 2 { fold := 5 q := 5  pow_bits := 25 qib := 24 vp := 32 }
                case 3 { fold := 5 q := 3  pow_bits := 32 qib := 24 vp := 32 }
                case 4 { fold := 4 q := 3  pow_bits := 17 qib := 25 vp := 16 }
                default { fold := 3 q := 2 pow_bits := 30 qib := 26 vp := 8 }
            }
            case 2 {
                // PACKED 8-col V=28 (search-optimal): folds=[2,4,4,4,5,5] lde2=[4,6,10,13,17,17]
                switch r
                case 0 { fold := 2 q := 13 pow_bits := 30 qib := 30 vp := 4 }
                case 1 { fold := 4 q := 9  pow_bits := 30 qib := 28 vp := 16 }
                case 2 { fold := 4 q := 5  pow_bits := 30 qib := 28 vp := 16 }
                case 3 { fold := 4 q := 4  pow_bits := 30 qib := 27 vp := 16 }
                case 4 { fold := 5 q := 3  pow_bits := 30 qib := 26 vp := 32 }
                default { fold := 5 q := 3 pow_bits := 30 qib := 21 vp := 32 }
            }
            default {
                // FULLYPACKED 1-col V=31, strict RS<=2^32 (DP-optimal):
                //   folds=[3,4,5,5,5,5] lde2=[1,4,8,13,17,17] q=[50,13,7,4,3,3] monomials=2^4
                //   round 0 LDE is forced to 2 (RS=31+1=32) => 50 queries.
                switch r
                case 0 { fold := 3 q := 50 pow_bits := 30 qib := 29 vp := 8 }
                case 1 { fold := 4 q := 13 pow_bits := 30 qib := 28 vp := 16 }
                case 2 { fold := 5 q := 7  pow_bits := 30 qib := 27 vp := 32 }
                case 3 { fold := 5 q := 4  pow_bits := 30 qib := 27 vp := 32 }
                case 4 { fold := 5 q := 3  pow_bits := 30 qib := 26 vp := 32 }
                default { fold := 5 q := 3 pow_bits := 30 qib := 21 vp := 32 }
            }
            let idx_mask := sub(shl(qib, 1), 1)

            for { let s := 0 } lt(s, fold) { s := add(s, 1) } {
                let cp := mload(REG_CD)
                let w0 := calldataload(cp)
                let c0 := shr(128, w0)
                let c1 := and(w0, MASK)
                let c2 := shr(128, calldataload(add(cp, 32)))
                calldatacopy(add(SEED_PTR, 32), cp, 48)
                mstore(SEED_PTR, keccak256(SEED_PTR, 80))
                let alpha := draw1()
                mstore(REG_CD, add(cp, 48))
                let p1 := addmod(c0, addmod(c1, c2, P), P)
                sink2(addmod(c0, p1, P), mload(REG_CLAIM))
                mstore(REG_CLAIM,
                    addmod(mulmod(addmod(mulmod(c2, alpha, P), c1, P), alpha, P), c0, P))
                mstore(add(FOLD_CH_PTR, mul(s, 32)), alpha)
                let zi_off := mload(REG_ZIOFF)
                fold_accumulator(alpha, mload(REG_NUMPOW), zi_off)
                mstore(REG_ZIOFF, add(zi_off, 32))
            }

            switch lt(r, 5)
            case 1 { do_internal(r, fold, q, pow_bits, qib, vp, idx_mask) }
            default { do_final(fold, q, pow_bits, qib, vp, idx_mask, mload(REG_ZIOFF), rfin) }
        }

        let verify_gas := sub(start_gas, gas())
        mstore(0, mload(REG_CLAIM))
        mstore(32, verify_gas)
        mstore(64, mload(REG_CD))
        mstore(96, mload(SINK_PTR))
        return(0, 128)
        }
    }
}

// =============================================================================
// Test / bench harness.  forge test -C verifier_evm --match-contract WhirVerifierTest -vv
// =============================================================================
contract WhirVerifierTest is WhirVerifier {
    event log_named_uint(string key, uint256 val);

    function test() external {
        // single hashed state commitment; verifier sinks the check so any value works
        assembly { sstore(0, keccak256(0, 32)) }
        bytes memory data = (new WhirStreamGen()).run();
        emit log_named_uint("calldata_bytes", data.length);
        uint256 g = gasleft();
        (bool ok, bytes memory ret) = address(this).call(data);
        g -= gasleft();
        require(ok, "whir verify reverted");
        (uint256 claim, uint256 verify_gas, uint256 cd, uint256 sink) =
            abi.decode(ret, (uint256, uint256, uint256, uint256));
        claim; sink;
        uint256 data_gas = calldata_gas(data);
        emit log_named_uint("proof_bytes_consumed", cd);
        emit log_named_uint("calldata_gas", data_gas);
        emit log_named_uint("verify_gas", verify_gas);
        emit log_named_uint("total_gas", 21000 + data_gas + verify_gas);
    }
}

function calldata_gas(bytes memory data) pure returns (uint256) {
    uint256 standard = 0; uint256 tokens = 0;
    for (uint256 i = 0; i < data.length; ++i) {
        if (data[i] == 0) { standard += 4; tokens += 1; }
        else { standard += 16; tokens += 4; }
    }
    uint256 eip7623 = 10 * tokens;
    return standard > eip7623 ? standard : eip7623;
}

// =============================================================================
// Stub proof-stream generator. Computes the exact byte length the verifier walks
// (preimage + per-round caps/leaves/paths) and fills with a nonzero pattern.
// Must mirror VARIANT / MERGED / CAP_LOG2.
// =============================================================================
contract WhirStreamGen {
    uint256 constant VARIANT  = 2;
    uint256 constant MERGED   = 1;
    uint256 constant CAP_LOG2 = 3;
    uint256 constant CAP      = 8;

    function run() external pure returns (bytes memory out) {
        uint8[6]  memory fold;
        uint8[6]  memory q;
        uint8[6]  memory qib;
        uint16[6] memory vp;
        uint256 rfin; uint256 nz; uint256 round0_cols; uint256 round0_trees; uint256 nbcaps;

        if (VARIANT == 0) {
            fold = [1, 5, 5, 5, 4, 3]; q = [13, 10, 5, 4, 3, 2];
            qib = [27, 23, 23, 23, 24, 25]; vp = [uint16(2), 32, 32, 32, 16, 8];
            rfin = 1; nz = 24; round0_cols = 113; round0_trees = MERGED == 1 ? 2 : 3;
        } else if (VARIANT == 1) {
            fold = [1, 5, 5, 5, 4, 3]; q = [10, 8, 5, 3, 3, 2];
            qib = [28, 24, 24, 24, 25, 26]; vp = [uint16(2), 32, 32, 32, 16, 8];
            rfin = 1; nz = 24; round0_cols = 113; round0_trees = MERGED == 1 ? 2 : 3;
        } else if (VARIANT == 2) {
            fold = [2, 4, 4, 4, 5, 5]; q = [13, 9, 5, 4, 3, 3];
            qib = [30, 28, 28, 27, 26, 21]; vp = [uint16(4), 16, 16, 16, 32, 32];
            rfin = 4; nz = 28; round0_cols = 9; round0_trees = 2;
        } else {
            // FULLYPACKED 1-col V=31, strict RS<=2^32
            fold = [3, 4, 5, 5, 5, 5]; q = [50, 13, 7, 4, 3, 3];
            qib = [29, 28, 27, 27, 26, 21]; vp = [uint16(8), 16, 32, 32, 32, 32];
            rfin = 4; nz = 31; round0_cols = 1; round0_trees = 1;
        }
        nbcaps = round0_trees;

        // preimage: seed + batching + opening + z (packed 2/word, ceil) + base caps
        uint256 total = 64 + ((nz + 1) / 2) * 32 + nbcaps * CAP * 32;

        for (uint256 r = 0; r < 6; ++r) {
            total += uint256(fold[r]) * 48;
            uint256 depth = uint256(qib[r]) - CAP_LOG2;
            if (r < 5) {
                total += CAP * 32 + 16 + 8;       // intermediate cap + ood + nonce
                for (uint256 i = 0; i < q[r]; ++i) {
                    if (r == 0) {
                        total += round0_cols * uint256(vp[r]) * 16;
                        total += round0_trees * depth * 32;
                    } else {
                        total += uint256(vp[r]) * 16 + depth * 32;
                    }
                }
            } else {
                total += (1 << rfin) * 16 + 8;    // monomials + nonce
                for (uint256 i = 0; i < q[r]; ++i) {
                    total += uint256(vp[r]) * 16 + depth * 32;
                }
            }
        }

        out = new bytes(total);
        assembly {
            let ptr := add(out, 32)
            let end := add(ptr, total)
            let pat := 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5
            for {} lt(ptr, end) { ptr := add(ptr, 32) } { mstore(ptr, pat) }
        }
    }
}
