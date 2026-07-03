// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.24;

// =============================================================================
// WHIR polynomial-commitment opening verifier (EVM skeleton)
// =============================================================================
//
// Hand-written EVM/Yul WHIR proximity-test verifier, sibling of gkr.sol. Every
// checked relation is a real assert via sink2() (reverts on mismatch). VARIANT 5
// verifies a real Proth120/Keccak proof from the `prover` crate's
// `generate_whir_input_for_evm` test (see WhirRealProofTest below).
//
// Field: P = 7*2^120 + 1 (Proth120, ~123 bit), one uint128/element, mulmod. keccak256
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
//                  [witness_cap : CAP*32][setup_cap : CAP*32]
//
// ---- Merkle caps ------------------------------------------------------------
// CAP_LOG2 = log2(cap size). Each commitment is a cap of 2^CAP_LOG2 hashes, so a
// Merkle path is CAP_LOG2 levels shorter. Caps shrink paths (saves
// total_paths*CAP_LOG2 sibling words) but grow every commitment to CAP*32 bytes.
//
// ---- Layout: 8 witness polys + 1 setup poly --------------------------------
// The witness oracle batches 8 columns into one Merkle tree, the setup oracle 1
// column into another; round 0 opens both (gamma-batched), later rounds fold the
// single intermediate oracle. VARIANT selects the message size:
//   4 = production: message 2^26, initial LDE 32 => RS codeword 2^31
//   5 = test:       message 2^8,  initial LDE 32 => RS codeword 2^13
// =============================================================================

contract WhirVerifier {
    // Field: Proth120, P = 7*2^120 + 1 (~123 bit), one uint128/element, mulmod.
    uint256 constant P    = 0x7000000000000000000000000000001;
    uint256 constant MASK = 0xffffffffffffffffffffffffffffffff;
    uint256 constant HALF = 0x3800000000000000000000000000001;  // 2^-1 = (P+1)/2
    // GEN = evaluation-domain generator for the RS codeword, GEN_INV = GEN^-1.
    // Yul inline-asm only accepts direct number constants, so keep the active
    // codeword's generator here and swap when changing VARIANT:
    //   VARIANT 4 (2^31): GEN=0x293B319B108C8A856BF8B8AB7799ECD
    //                     GEN_INV=0x290A0CB0CAD8AC9DAFCDC73EBD1A223
    //   VARIANT 5 (2^13): GEN=0x029ef460f7f59242f45befd0fa65241e
    //                     GEN_INV=0x00cb35491d13c704939bb02be3b31e21
    uint256 constant GEN     = 0x0293B319B108C8A856BF8B8AB7799ECD;
    uint256 constant GEN_INV = 0x0290A0CB0CAD8AC9DAFCDC73EBD1A223;

    uint256 constant NUM_ROUNDS = 6;
    // Message size selector (8 witness + 1 setup polys, both sizes):
    //   4 = production (message 2^26, RS codeword 2^31)
    //   5 = test       (message 2^8,  RS codeword 2^13)
    uint256 constant VARIANT  = 4;
    // Must match the prover's `eval_leaves` cargo feature. 0 (default): intermediate
    // oracles commit multilinear-COEFFICIENT leaves -> fold with the plain monomial
    // tensor (fold_multilinear). 1 (eval_leaves): they commit raw EVALUATIONS -> fold
    // with the coset base-root (fold_coset), like the round-0 base oracle.
    uint256 constant EVAL_LEAVES = 0;
    // cap size knob: keep CAP == 2^CAP_LOG2 in sync (Yul needs literal constants).
    uint256 constant CAP_LOG2 = 3;
    uint256 constant CAP      = 8;

    // ── hand-placed memory ────────────────────────────────────────────────────
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
    // cap regions (each holds up to CAP*32 bytes)
    uint256 constant BCAP0_PTR    = 23296;  // witness base-oracle cap
    uint256 constant BCAP1_PTR    = 24320;  // setup base-oracle cap
    uint256 constant QCAP_PTR     = 26368;  // current query cap (rounds >= 1)
    uint256 constant NCAP_PTR     = 27392;  // just-read intermediate cap
    // Per-round query drawing (matches prover `draw_query_bits`/`BitSource`):
    //   QIDX_BUF holds the drawn query indices (<= 50 * 32 bytes);
    //   DRAW_BUF holds the little-endian u32 words squeezed from the seed.
    uint256 constant QIDX_BUF_PTR = 28416;  // drawn query indices
    uint256 constant DRAW_BUF_PTR = 30016;  // squeezed LE u32 words (one per slot)

    fallback() external {
        assembly {
        // Every checked WHIR relation flows through here: revert unless equal.
        function sink2(a, b) {
            let c := add(mload(0xF000), 1)
            mstore(0xF000, c)
            if iszero(eq(a, b)) { mstore(0, c) mstore(32, a) mstore(64, b) revert(0, 96) }
        }
        function draw1() -> r {
            let s := keccak256(SEED_PTR, 32)
            mstore(SEED_PTR, s)
            // top 128 bits reduced mod P (matches prover `from_u128_with_reduction`).
            // Reduction is required: unreduced values break `sub(P, x)` for x > P.
            r := mod(shr(128, s), P)
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
        // Draw `num_q` query indices exactly as the prover's `draw_query_bits`:
        // squeeze `padded` little-endian u32 words from the seed (8 words per
        // keccak block, re-hashing the seed before each block), DROP the first
        // word, then read `qib` bits per index LSB-first from the remaining
        // stream (BitSource + assemble_query_index). Indices land in QIDX_BUF.
        function draw_queries(num_q, qib) {
            let num_bits := mul(num_q, qib)
            // num_required_words = next_multiple_of(num_bits, 32) / 32
            let nrw := shr(5, and(add(num_bits, 31), not(31)))
            // padded = next_multiple_of(nrw + 1, 8)
            let padded := and(add(add(nrw, 1), 7), not(7))
            let wi := 0
            for {} lt(wi, padded) {} {
                let d := keccak256(SEED_PTR, 32)
                mstore(SEED_PTR, d)
                for { let j := 0 } and(lt(j, 8), lt(wi, padded)) { j := add(j, 1) } {
                    let b := mul(j, 4)
                    // little-endian u32 from digest bytes [b, b+4)
                    let w := or(
                        or(byte(b, d), shl(8, byte(add(b, 1), d))),
                        or(shl(16, byte(add(b, 2), d)), shl(24, byte(add(b, 3), d))))
                    mstore(add(DRAW_BUF_PTR, mul(wi, 32)), w)
                    wi := add(wi, 1)
                }
            }
            // skip the first squeezed word => start at global bit 32
            for { let qq := 0 } lt(qq, num_q) { qq := add(qq, 1) } {
                let base_bit := add(32, mul(qq, qib))
                let idx := 0
                for { let k := 0 } lt(k, qib) { k := add(k, 1) } {
                    let gb := add(base_bit, k)
                    let word := mload(add(DRAW_BUF_PTR, mul(shr(5, gb), 32)))
                    idx := or(idx, shl(k, and(shr(and(gb, 31), word), 1)))
                }
                mstore(add(QIDX_BUF_PTR, mul(qq, 32)), idx)
            }
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
        // Plain multilinear fold (monomial tensor eval) with the fold challenges,
        // WITHOUT the coset base-root. Used for INTERMEDIATE/FINAL oracle leaves,
        // whose stored values fold as f = e0 + e1*ch per step (the prover's default
        // `eval_multilinear_with_monomial_tensor` path, no `evals_to_multilinear_coeffs`).
        function fold_multilinear(fold) -> folded {
            let n := shl(fold, 1)
            for { let round := 0 } lt(round, fold) { round := add(round, 1) } {
                let half := shr(1, n)
                let ch := mload(add(FOLD_CH_PTR, mul(round, 32)))
                for { let i := 0 } lt(i, half) { i := add(i, 1) } {
                    let a := mload(add(FBUF_PTR, mul(mul(i, 2), 32)))
                    let b := mload(add(FBUF_PTR, mul(add(mul(i, 2), 1), 32)))
                    mstore(add(FBUF_PTR, mul(i, 32)), addmod(a, mulmod(b, ch, P), P))
                }
                n := half
            }
            folded := mload(FBUF_PTR)
        }
        // Merkle path of `depth` levels (already cap-reduced), then match a cap
        // entry. depth = query_index_bits - CAP_LOG2.
        //
        // The prover splits the query index the same way and lays out tree leaves
        // as [ bitreverse(coset_index) | internal_index ]:
        //   coset_index    = the low `coset_bits` bits of `qidx`
        //   internal_index = the remaining high bits
        // so the internal-index bits occupy the low (leaf-side) positions of the
        // physical tree index and the bit-reversed coset bits occupy the high
        // (cap-side) positions. We therefore walk the path over internal-index
        // bits first (LSB-first), then over coset-index bits in bit-reversed order
        // (MSB-first). The first `depth` bits form the Merkle path; the remaining
        // top bits index the cap. Each level orders current/sibling by its bit:
        // keccak(current || sibling) for a left child, keccak(sibling || current)
        // for a right child.
        function merkle_path(leaf_hash, depth, cap_ptr, cp, qidx, coset_bits) -> next_cd {
            let qib := add(depth, CAP_LOG2)
            let internal_bits := sub(qib, coset_bits)
            let internal_index := shr(coset_bits, qidx)
            let coset_index := and(qidx, sub(shl(coset_bits, 1), 1))

            let h := leaf_hash
            let cap_index := 0
            for { let pos := 0 } lt(pos, qib) { pos := add(pos, 1) } {
                // Bit of the physical tree index at position `pos` (LSB == leaf side).
                let bit
                switch lt(pos, internal_bits)
                case 1 {
                    bit := and(shr(pos, internal_index), 1)
                }
                default {
                    // Bit-reversed coset bit: path position `internal_bits + j`
                    // reads coset bit `coset_bits - 1 - j`.
                    let j := sub(pos, internal_bits)
                    bit := and(shr(sub(sub(coset_bits, 1), j), coset_index), 1)
                }

                switch lt(pos, depth)
                case 1 {
                    let sibling := calldataload(cp)
                    cp := add(cp, 32)
                    switch bit
                    case 0 {
                        // current node is the left child
                        mstore(0, h)
                        mstore(32, sibling)
                    }
                    default {
                        // current node is the right child
                        mstore(0, sibling)
                        mstore(32, h)
                    }
                    h := keccak256(0, 64)
                }
                default {
                    // Bits above the path form the cap index.
                    cap_index := or(cap_index, shl(sub(pos, depth), bit))
                }
            }
            sink2(h, mload(add(cap_ptr, mul(cap_index, 32)))) // match h against cap[cap_index]
            next_cd := cp
        }
        function batch_oracle(cp, cols, goff, vp, depth, cap_ptr, qidx, cb) -> next_cd {
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
            next_cd := merkle_path(keccak256(LEAF_PTR, mul(li, 32)), depth, cap_ptr, cp, qidx, cb)
        }
        function read_leaf(cp, vp, depth, cap_ptr, qidx, cb) -> next_cd {
            let words := shr(1, vp)
            for { let i := 0 } lt(i, words) { i := add(i, 1) } {
                let w := calldataload(cp)
                mstore(add(LEAF_PTR, mul(i, 32)), w)
                mstore(add(FBUF_PTR, mul(mul(i, 2), 32)), shr(128, w))
                mstore(add(FBUF_PTR, mul(add(mul(i, 2), 1), 32)), and(w, MASK))
                cp := add(cp, 32)
            }
            next_cd := merkle_path(keccak256(LEAF_PTR, mul(words, 32)), depth, cap_ptr, cp, qidx, cb)
        }
        // Reinterpret a 32-byte digest (8 big-endian u32 words) as the same 8
        // words each in little-endian byte order, keeping word positions. This
        // matches the prover's `commit_u32` cap absorption (LE u32 word bytes)
        // while the raw BE digest is still used for Merkle-root comparison.
        function bswap_digest(d) -> s {
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                let sh := sub(224, mul(i, 32))
                let w := and(shr(sh, d), 0xffffffff)
                let sw := or(
                    or(shl(24, and(w, 0xff)), shl(8, and(w, 0xff00))),
                    or(and(shr(8, w), 0xff00), and(shr(24, w), 0xff)))
                s := or(s, shl(sh, sw))
            }
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

        function do_query(r, fold, qib, vp, idx_mask, delin, cb, qq) {
            let cp := mload(REG_CD)
            let cur := mulmod(mload(REG_CURDELIN), delin, P)
            mstore(REG_CURDELIN, cur)
            let qidx := and(mload(add(QIDX_BUF_PTR, mul(qq, 32))), idx_mask)
            let base_root_inv := powmod(GEN_INV, qidx)
            let depth := sub(qib, CAP_LOG2)

            switch r
            case 0 {
                // Round 0 queries the base oracles: 8 witness columns (BCAP0) then
                // 1 setup column (BCAP1), gamma-batched into the folding buffer.
                for { let j := 0 } lt(j, vp) { j := add(j, 1) } { mstore(add(FBUF_PTR, mul(j, 32)), 0) }
                cp := batch_oracle(cp, 8, 0, vp, depth, BCAP0_PTR, qidx, cb)
                cp := batch_oracle(cp, 1, 8, vp, depth, BCAP1_PTR, qidx, cb)
            }
            default {
                cp := read_leaf(cp, vp, depth, QCAP_PTR, qidx, cb)
            }
            mstore(REG_CD, cp)
            // round 0 queries a base oracle (coset fold); later rounds query
            // intermediate oracles (plain multilinear fold, no base-root).
            let folded
            // round 0 (base oracle) always folds evals with the coset base-root;
            // intermediate rounds fold coeff leaves (fold_multilinear) unless the
            // prover used eval_leaves, in which case they too are raw evals.
            switch or(iszero(r), EVAL_LEAVES)
            case 1 { folded := fold_coset(fold, base_root_inv) }
            default { folded := fold_multilinear(fold) }
            push_pow(exp_pow2(powmod(GEN, qidx), fold), cur)
            mstore(REG_CC, addmod(mload(REG_CC), mulmod(folded, cur, P), P))
        }

        function do_internal(r, fold, q, pow_bits, qib, vp, idx_mask, cb) {
            let cp := mload(REG_CD)
            // read + absorb the next oracle's CAP (CAP*32 bytes)
            // keep BE digests for Merkle roots; absorb LE-word copies (commit_u32)
            for { let i := 0 } lt(i, CAP) { i := add(i, 1) } {
                let d := calldataload(add(cp, mul(i, 32)))
                mstore(add(NCAP_PTR, mul(i, 32)), d)
                mstore(add(SEED_PTR, add(32, mul(i, 32))), bswap_digest(d))
            }
            mstore(SEED_PTR, keccak256(SEED_PTR, add(32, mul(CAP, 32))))
            cp := add(cp, mul(CAP, 32))
            let ood_point := draw1()
            let ood_value := shr(128, calldataload(cp))
            calldatacopy(add(SEED_PTR, 32), cp, 16)
            mstore(SEED_PTR, keccak256(SEED_PTR, 48))
            cp := add(cp, 16)
            cp := verify_pow(cp, pow_bits)
            // prover order: PoW -> draw query bits -> draw delinearization
            draw_queries(q, qib)
            let delin := draw1()
            mstore(REG_CD, cp)
            push_pow(ood_point, delin)
            mstore(REG_CC, mulmod(ood_value, delin, P))
            mstore(REG_CURDELIN, delin)
            compute_hpo(fold)
            for { let qq := 0 } lt(qq, q) { qq := add(qq, 1) } {
                do_query(r, fold, qib, vp, idx_mask, delin, cb, qq)
            }
            mstore(REG_CLAIM, addmod(mload(REG_CLAIM), mload(REG_CC), P))
            copy_cap(QCAP_PTR, NCAP_PTR) // this round's intermediate cap is next round's query cap
        }

        function do_final(fold, q, pow_bits, qib, vp, idx_mask, zi_off, rfin, cb) {
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
            draw_queries(q, qib)
            compute_hpo(fold)
            let depth := sub(qib, CAP_LOG2)

            for { let qq := 0 } lt(qq, q) { qq := add(qq, 1) } {
                let qidx := and(mload(add(QIDX_BUF_PTR, mul(qq, 32))), idx_mask)
                let base_root := powmod(GEN, qidx)
                cp := read_leaf(cp, vp, depth, QCAP_PTR, qidx, cb)
                // final round queries an intermediate oracle: coeff leaves fold with
                // the plain monomial tensor, unless eval_leaves (raw evals -> fold_coset).
                let folded
                switch EVAL_LEAVES
                case 1 { folded := fold_coset(fold, powmod(GEN_INV, qidx)) }
                default { folded := fold_multilinear(fold) }
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

        // 8 witness + 1 setup poly -> 9 batched columns, 2 base caps (witness,setup).
        //   VARIANT 4 (prod):  message 2^26, final poly 2^4 monomials (rfin 4)
        //   VARIANT 5 (test):  message 2^8,  final poly 2^2 monomials (rfin 2)
        let nz := 26
        let gcount := 9
        let rfin := 4
        let nbcaps := 2
        if eq(VARIANT, 5) { nz := 8 rfin := 2 }

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
        // base caps: witness (BCAP0) then setup (BCAP1)
        let caps_off := add(64, mul(zwords, 32))
        calldatacopy(BCAP0_PTR, caps_off, mul(CAP, 32))
        calldatacopy(BCAP1_PTR, add(caps_off, mul(CAP, 32)), mul(CAP, 32))
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
            // `cb` = coset bits = log2(LDE factor) for this round's oracle tree.
            let fold, q, pow_bits, qib, vp, cb
            switch VARIANT
            case 4 {
                // PROTH120: 8 witness + 1 setup poly of 2^26 (message), initial LDE
                // factor 32 (=2^5). Every round's RS codeword stays 2^31, so the LDE
                // factor grows as the message folds down:
                //   folds=[2,4,4,4,4,4] (sum 22 => final 2^4=16 monomials)
                //   message_r = 2^(26 - prefolds), lde2_r = log2(2^31/message_r) = 5+prefolds
                //   qib_r  = log2(codeword/vp) = 31 - fold_r
                //   cb_r   = lde2_r (coset bits)
                // Queries for 100-bit security under the pessimistic conjecture.
                //   bits/query = cb (= log2 LDE); q = ceil(1.2 * (100 - pow_bits) / cb)
                //   (20% margin over the conjecture, exact ceiling, no floor rounding).
                // pow_bits is then reduced per round to the smallest value that leaves
                // q unchanged (each round still yields >= 100 bits = pow + q*cb/1.2).
                // All q are far below the 2^32 query-domain cap.
                switch r
                case 0 { fold := 2 q := 17 pow_bits := 30 qib := 29 vp := 4  cb := 5 }
                case 1 { fold := 4 q := 12 pow_bits := 30 qib := 27 vp := 16 cb := 7 }
                case 2 { fold := 4 q := 8  pow_bits := 27 qib := 27 vp := 16 cb := 11 }
                case 3 { fold := 4 q := 6  pow_bits := 25 qib := 27 vp := 16 cb := 15 }
                case 4 { fold := 4 q := 5  pow_bits := 21 qib := 27 vp := 16 cb := 19 }
                default { fold := 4 q := 4 pow_bits := 24 qib := 27 vp := 16 cb := 23 }
            }
            default {
                // PROTH120 TEST (matches prover proth120_evm_gen): 8 witness + 1 setup
                // poly of 2^8 (message), initial LDE 32 => RS codeword 2^13. Every
                // round folds by 1, so message halves and LDE doubles, codeword stays
                // 2^13. vp = 2^fold = 2; qib = log2(codeword/vp) = 12; cb = log2(LDE).
                //   folds=[1,1,1,1,1,1] (final 2^2 = 4 monomials), q=2, pow=0.
                switch r
                case 0 { fold := 1 q := 2 pow_bits := 0 qib := 12 vp := 2 cb := 5 }
                case 1 { fold := 1 q := 2 pow_bits := 0 qib := 12 vp := 2 cb := 6 }
                case 2 { fold := 1 q := 2 pow_bits := 0 qib := 12 vp := 2 cb := 7 }
                case 3 { fold := 1 q := 2 pow_bits := 0 qib := 12 vp := 2 cb := 8 }
                case 4 { fold := 1 q := 2 pow_bits := 0 qib := 12 vp := 2 cb := 9 }
                default { fold := 1 q := 2 pow_bits := 0 qib := 12 vp := 2 cb := 10 }
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
            case 1 { do_internal(r, fold, q, pow_bits, qib, vp, idx_mask, cb) }
            default { do_final(fold, q, pow_bits, qib, vp, idx_mask, mload(REG_ZIOFF), rfin, cb) }
        }

        // Every check passed (any failure would have reverted). Return the final
        // claim, the gas used, and the number of proof bytes consumed.
        let verify_gas := sub(start_gas, gas())
        mstore(0, mload(REG_CLAIM))
        mstore(32, verify_gas)
        mstore(64, mload(REG_CD))
        return(0, 96)
        }
    }
}

// =============================================================================
// Test harness. Feeds the REAL prover-generated calldata (the VARIANT 5 fixture
// from `prover` test `generate_whir_input_for_evm`). The verifier reverts on any
// failed relation, so a successful call == a valid proof.
//   forge test -C verifier_evm --match-contract WhirRealProofTest -vv
// =============================================================================
interface WhirVm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata s) external pure returns (bytes memory);
}

contract WhirRealProofTest is WhirVerifier {
    event log_named_uint(string key, uint256 val);
    WhirVm constant vm = WhirVm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    // VARIANT 4 preimage length: 64 + ceil(nz/2)*32 + nbcaps*CAP*32
    //                          = 64 + 13*32 + 2*8*32 = 992
    uint256 constant PLEN = 992;

    function test() external {
        string memory h = vm.readFile("whir/testdata/proth120_whir_calldata_prod.hex");
        bytes memory data = vm.parseBytes(string.concat("0x", h));
        // bind the preimage to storage slot 0 (stand-in for the on-chain commitment)
        bytes32 ph;
        assembly { ph := keccak256(add(data, 32), PLEN) }
        assembly { sstore(0, ph) }
        emit log_named_uint("calldata_bytes", data.length);
        (bool ok, bytes memory ret) = address(this).call(data);
        if (!ok) {
            (uint256 sinkIdx, uint256 a, uint256 b) = abi.decode(ret, (uint256, uint256, uint256));
            emit log_named_uint("failed_sink_index", sinkIdx);
            emit log_named_uint("sink_a", a);
            emit log_named_uint("sink_b", b);
        }
        require(ok, "whir verify reverted");
        (uint256 claim, uint256 verify_gas, uint256 cd) =
            abi.decode(ret, (uint256, uint256, uint256));
        emit log_named_uint("proof_bytes_consumed", cd);
        emit log_named_uint("verify_gas", verify_gas);
        emit log_named_uint("final_claim", claim);
        require(cd == data.length, "stream not fully consumed");
    }
}
