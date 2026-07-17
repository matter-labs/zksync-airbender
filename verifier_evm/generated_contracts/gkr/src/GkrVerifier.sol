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
    uint256 constant MINIMUM_FREE_HEAP_PTR = 7588;
    uint256 constant P      = 0x7000000000000000000000000000001; // Proth120: 7*2^120 + 1
    uint256 constant MASK   = 0xffffffffffffffffffffffffffffffff; // high 128 bits (one field lane)
    // Stack-pressure fix: the ~123-bit modulus P as a literal is a PUSH16 rematerialized at
    // every addmod/mulmod, and the Yul scheduler keeps it live across the deep gate sequences
    // (→ "stack too deep"). Store P once at a small heap offset and `mload(P_PTR)` it instead
    // (PUSH1 offset + MLOAD, consumed immediately, not kept live). The generated circuit.yul
    // and the hand-written ops both use `mload(P_PTR)`; `mstore(P_PTR, mload(P_PTR))` runs first in the
    // fallback. P_PTR is below the hand-placed heap (MINIMUM_FREE_HEAP_PTR) and above the
    // 0..128 return/scratch region.
    uint256 constant P_PTR  = 160;
    // Fixed heap slot holding the circuit-layer calldata cursor, so gate/cache sub-functions
    // read it via mload instead of a `ptr` parameter (that param was the single deepest stack
    // slot pushing each of them 1 over the EVM limit). Sits just above P_PTR (160..191).
    uint256 constant CIRCUIT_PTR = 192;
    uint256 constant ROUNDS = 200;

    // ── Transcript init (absorb caps, derive memory/logup challenges) ─────────
    uint256 constant MERKLE_TREE_CAPS_BYTES = 512; // 16 caps * 32-byte hash
    // Proth120 packed-mode: keccak preimage = commit_initial_u32 bytes
    // (inits_and_teardowns_top_bits as LE u32 || setup cap digests || merged mem cap digests).
    // 520 for this proof (unified_reduced_machine, 2^22, pack_log2=4). See gkr_transcript_reference.md.
    uint256 constant GKR_INIT_PREIMAGE_BYTES = 916; // registers(384) + final_pc(12) + top_bits(8) + setup_cap(256) + memory_cap(256)
    uint256 constant EXTERNAL_POW_BITS       = 20;  // external-challenge PoW difficulty (max(lookup, 20))
    uint256 constant EXPECTED_FINAL_PC       = 384; // program's terminal PC — binds the verified statement to this program

    // ── GKR init (fold the 8 init polys into the first sumcheck claim) ────────
    uint256 constant GKR_INIT_BYTES          = 2560; // 10 output polys * 16 elems * 16 bytes (Proth120)
    uint256 constant GKR_INIT_POLY_BYTES     = 256;  // 16 elems * 16 bytes (literal; Yul rejects const exprs)

    // ── GKR compression ───────────────────────────────────────────────────────
    uint256 constant GKR_COMPRESSION_POINTCHECK_POLY_BYTES = 64;  // 4 * 16
    uint256 constant GKR_COMPRESSION_POINTCHECK_BYTES      = 512; // 8 * 64

    // ── GKR circuit ───────────────────────────────────────────────────────────
    uint256 constant GKR_CIRCUIT_LAYER_ROUNDS = 22;

    // ── Committed-state handoff to WHIR (via the shared registry) ──────────────
    // After GKR verifies, it assembles the SAME committed-state preimage the WHIR
    // verifier hashes — [seed:32][batching:16][opening:16][z_initial:nz*16]
    // [witness_cap:CAP*32][setup_cap:CAP*32] — keccaks it, and marks it. WHIR
    // recomputes the same bytes32 in its own tx; the registry events must match.
    uint256 constant REGISTRY          = 0xCAFE0001;
    uint256 constant MARK_GKR_SELECTOR = 0xef4f148a; // mark_gkr_verified(bytes32,bytes32,bytes32)
    uint256 constant WHIR_Z_COORDS     = 26;         // 22 base + 4 packing extra coords
    uint256 constant WHIR_CAP          = 8;          // CAP (witness+setup base-oracle caps)
    uint256 constant WHIR_BATCH_POW_BITS = 11;       // batched_proximity_check_pow_bits (Sec100)
    // GKR->WHIR handoff (MergedAndPackedMemoryAndWitness, pack_log2=4). Base-layer at-point
    // claims (dense in layer0's calldata eval block): mem++wit = 104 cols, setup = 10 cols.
    // Merge folds each 2^pack_log2=16-chunk by the 4 packing coords: 104->7, 10->1.
    uint256 constant WHIR_PACK_LOG2    = 4;
    uint256 constant WHIR_NUM_MEMWIT   = 104;        // memory_layout + witness_layout total widths
    uint256 constant WHIR_NUM_SETUP    = 10;         // generic_lookup_tables_width
    uint256 constant WHIR_MERGED_MW    = 7;          // ceil(104/16)
    uint256 constant WHIR_BASE_Z_COORDS = 22;        // layer-0 folding point length

    fallback() external {
        // uint256 variant = VARIANT;
        // NOTE: "memory-safe" is TRANSIENT — it lets solc spill the 1 leftover stack slot in the
        // OLD sumcheck_compress_2pass (dim-reducing, pending replacement by the validated
        // GkrDimReduce logic). The hand-placed memory is disjoint from spill slots, but
        // re-audit memory-safety once the dim-reducing port lands.
        assembly ("memory-safe") {
        mstore(P_PTR, 0x7000000000000000000000000000001)
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
        function SEED_PTR() -> ptr {
            ptr := add(GKR_MAIN_GAS_PTR(), mul(32, 1))
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
        // Dim-reducing / entry regions (used before the circuit layers; placed well above the
        // transcript scratch that the sumcheck rounds clobber at SEED±96).
        function GKR_BATCHING_PTR() -> ptr { ptr := add(SEED_PTR(), mul(32, 40)) }      // running batching
        function GKR_CLAIMS_PTR()   -> ptr { ptr := add(SEED_PTR(), mul(32, 41)) }      // 10 dim-reduce claims
        function GKR_EQ_PTR()       -> ptr { ptr := add(SEED_PTR(), mul(32, 52)) }      // eq[16] for entry claims
        function GKR_ABS_PTR()      -> ptr { ptr := add(SEED_PTR(), mul(32, 70)) }      // absorb scratch (32+2560)
        // Circuit-layer claims array (STEP 3): the previous circuit layer's at-point evals,
        // offset-indexed, that this layer's `compute_claim` batches into its initial claim.
        // Threaded across layers: each layer writes its input evals here for the next one.
        // Placed above GKR_ABS_PTR's 32+2560 scratch. Sized for the widest layer (<128).
        function GKR_CIRCUIT_CLAIMS_PTR() -> ptr {
        ptr := add(SEED_PTR(), mul(32, 160)) }

        // Permutation-identity products: read_poly, write_poly, teardown_poly, init_poly
        // (∏ of each relevant GKR output poly's 16 elements). Filled in gkr_init, consumed by
        // check_permutation_identity. Sits in the free window between GKR_ABS scratch and
        // GKR_CIRCUIT_CLAIMS (slots 152..155), untouched by compress/circuit.
        function GKR_PERM_PROD_PTR() -> ptr {
        ptr := add(SEED_PTR(), mul(32, 152)) }

        // Read one little-endian u32 from the transcript preimage (absolute calldata byteoff).
        function preimage_u32(byteoff) -> v {
            let w := calldataload(byteoff)
            v := add(add(byte(0, w), shl(8, byte(1, w))), add(shl(16, byte(2, w)), shl(24, byte(3, w))))
        }

        function transcript_4to1_dual(w0, w1) -> r {
            // Proth120 recipe (validated in step1_test/GkrCompressYul): ABSORB the 4 coeffs
            // (seed = keccak(seed || w0 || w1)) THEN DRAW (seed = keccak(seed); r = top128 mod P).
            // The prior code drew straight from the absorb result (missing the draw keccak) — a
            // leftover of the old field's convention; it corrupts every round after the first.
            mstore(add(SEED_PTR(), 64), w1)
            mstore(add(SEED_PTR(), 32), w0)
            let seed := keccak256(SEED_PTR(), 96) // absorb 4 coeffs
            mstore(SEED_PTR(), seed)
            seed := keccak256(SEED_PTR(), 32)     // draw
            mstore(SEED_PTR(), seed)
            r := mod(shr(128, seed), mload(P_PTR))
        }

        // alpha is the batching challenge needed right after checking outputs



        // alpha is the batching challenge needed right folding point claims

        function transcript_init(ptr) -> next_ptr {
            // Proth120 packed-mode transcript (MergedAndPackedMemoryAndWitness), validated
            // keccak-for-keccak in step1_test/GkrStep1.sol against the real proof.
            //   seed = keccak256(preimage)                       // commit_initial_u32 (916 B: regs+PC+topbits+caps)
            //   nonce = calldata[preimage..preimage+8] (BE u64)
            //   seed = keccak256(seed || be8(nonce)); require top EXTERNAL_POW_BITS bits zero
            //   for i in 0..9: seed = keccak256(seed); ch = (seed>>128) % P
            //   ch[0..7] -> MEMORY_CHALLS (6 perm-linearization + additive), ch[7..9] -> LOGUP (alpha, additive)
            calldatacopy(SEED_PTR(), ptr, GKR_INIT_PREIMAGE_BYTES)
            let seed := keccak256(SEED_PTR(), GKR_INIT_PREIMAGE_BYTES)

            // PoW fold: digest = keccak(seed(32) || nonce_be8); require top EXTERNAL_POW_BITS zero.
            let nonce := shr(192, calldataload(add(ptr, GKR_INIT_PREIMAGE_BYTES))) // 8-byte BE nonce
            mstore(SEED_PTR(), seed)
            mstore(add(SEED_PTR(), 32), shl(192, nonce))
            seed := keccak256(SEED_PTR(), 40)
            if shr(sub(256, EXTERNAL_POW_BITS), seed) { revert(0, 0) } // PoW: top pow_bits must be zero

            // draw 9 challenges (each: seed=keccak(seed); take top 128 bits mod P)
            mstore(SEED_PTR(), seed)
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            mstore(MEMORY_CHALLS_PTR(),               mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            mstore(add(MEMORY_CHALLS_PTR(), 32),       mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            mstore(add(MEMORY_CHALLS_PTR(), 64),       mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            mstore(add(MEMORY_CHALLS_PTR(), 96),       mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            mstore(add(MEMORY_CHALLS_PTR(), 128),      mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            mstore(add(MEMORY_CHALLS_PTR(), 160),      mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            mstore(add(MEMORY_CHALLS_PTR(), 192),      mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            mstore(LOGUP_CHALLS_PTR(),                 mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            mstore(add(LOGUP_CHALLS_PTR(), 32),        mod(shr(128, seed), mload(P_PTR)))

            // SEED_PTR now holds the post-STEP-1 seed; the GKR entry (gkr_init) absorbs output evals next.
            next_ptr := add(ptr, add(GKR_INIT_PREIMAGE_BYTES, 8)) // preimage + 8-byte PoW nonce
        }



        // Strategy 2: absorb the init block and draw z1..z4 and alpha, but do not
        // store full eq[16]. Instead, generate eq factors inline while streaming
        // over calldata so folding and accumulator updates happen in one pass.
        // GKR entry (STEP 2a). Validated keccak-for-keccak against GkrStep1.gkrEntry
        // (step1_test/GkrInitYul.t.sol): continue from the post-STEP-1 seed, absorb the 2560 B
        // of output evals, draw eval_point[4] (→ POINT_PTR) + batching (→ GKR_BATCHING_PTR).
        // Then compute the 10 dim-reducing claims: eq[16] over eval_point, dotted with each of
        // the 10 output columns (matches the validated Rust mirror). claim/alpha are legacy
        // returns kept 0 — gkr_compress reads GKR_CLAIMS_PTR / GKR_BATCHING_PTR.
        function gkr_init(ptr) -> next_ptr, claim, alpha {
            let sp := SEED_PTR()
            // absorb output evals: seed = keccak(seed || outputEvals)
            mstore(GKR_ABS_PTR(), mload(sp))
            calldatacopy(add(GKR_ABS_PTR(), 32), ptr, GKR_INIT_BYTES)
            let seed := keccak256(GKR_ABS_PTR(), add(32, GKR_INIT_BYTES))
            mstore(sp, seed)
            // draw eval_point[4] -> POINT_PTR, then batching -> GKR_BATCHING_PTR
            for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                seed := keccak256(sp, 32)
                mstore(sp, seed)
                mstore(add(POINT_PTR(), mul(i, 32)), mod(shr(128, seed), mload(P_PTR)))
            }
            seed := keccak256(sp, 32)
            mstore(sp, seed)
            mstore(GKR_BATCHING_PTR(), mod(shr(128, seed), mload(P_PTR)))

            // eq[16] over eval_point[4] (MSB-first: eq[j] = Π_v (bit_{3-v}(j)? z[v] : 1-z[v]))
            for { let j := 0 } lt(j, 16) { j := add(j, 1) } {
                let e := 1
                for { let v := 0 } lt(v, 4) { v := add(v, 1) } {
                    let zv := mload(add(POINT_PTR(), mul(v, 32)))
                    let bit := and(shr(sub(3, v), j), 1)
                    // f = bit ? zv : (1 - zv)   (non-canonical 1-zv = 1 + (P - zv))
                    let f := zv
                    if iszero(bit) {
                    f := add(1, sub(mload(P_PTR), zv)) }
                    e := mulmod(e, f, mload(P_PTR))
                }
                mstore(add(GKR_EQ_PTR(), mul(j, 32)), e)
            }
            // 10 claims: claim_c = Σ_j outputEval[c*16+j] * eq[j]  (column c, 16 evals).
            // Also accumulate ∏ of the 16 elements for the permutation-identity outputs:
            // BTreeMap<OutputType> order => [0]=Perm.read, [1]=Perm.write, [8]=I&T.teardown,
            // [9]=I&T.init (validated in verify_permutation_identity_no_inversion).
            for { let c := 0 } lt(c, 10) { c := add(c, 1) } {
                let acc := 0
                let prod := 1
                for { let j := 0 } lt(j, 16) { j := add(j, 1) } {
                    let k := add(mul(c, 16), j)
                    let val := shr(128, calldataload(add(ptr, mul(k, 16))))
                    acc := add(mulmod(val, mload(add(GKR_EQ_PTR(), mul(j, 32))), mload(P_PTR)), acc)
                    prod := mulmod(prod, val, mload(P_PTR))
                }
                mstore(add(GKR_CLAIMS_PTR(), mul(c, 32)), mod(acc, mload(P_PTR)))
                // stash the 4 permutation-identity products (read=0, write=1, teardown=8, init=9)
                switch c
                case 0 { mstore(add(GKR_PERM_PROD_PTR(), 0),  prod) }
                case 1 { mstore(add(GKR_PERM_PROD_PTR(), 32), prod) }
                case 8 { mstore(add(GKR_PERM_PROD_PTR(), 64), prod) }
                case 9 { mstore(add(GKR_PERM_PROD_PTR(), 96), prod) }
            }
            next_ptr := add(ptr, GKR_INIT_BYTES)
        }

        // Permutation identity check (no inversions). The prover's grand-product self-check is
        //   (write_poly/read_poly)*(init_poly/teardown_poly)*(machine_write/machine_read) == 1.
        // Multiplying out gives the inverse-free equality the EVM verifier enforces instead:
        //   read_poly * teardown_poly * read_bnd  ==  write_poly * init_poly * write_bnd
        // where read_bnd/write_bnd are the register + PC boundary contributions built from the
        // register final state and PC in the transcript preimage (validated in the Rust mirror
        // verify_permutation_identity_no_inversion). Challenge/addr-space/index constants:
        //   perm-lin challenges mc[0..5]: ADDR_LOW=0, ADDR_HIGH=1, TS_LOW=2, TS_HIGH=3,
        //   VALUE_LOW=4, VALUE_HIGH=5; additive = mc@192. PC modeled as memory cell:
        //   PC_LOW=VALUE_LOW=4, PC_HIGH=VALUE_HIGH=5, PC_TS_LOW=2, PC_TS_HIGH=3.
        //   AddressSpaceType: Register=0, PC=2. INITIAL_PC=0, split(INITIAL_TIMESTAMP=4)=(4,0).
        function check_permutation_identity() {
            let Pm := mload(P_PTR)
            let mc := MEMORY_CHALLS_PTR()
            let mc0 := mload(mc)
            let mc2 := mload(add(mc, 64))
            let mc3 := mload(add(mc, 96))
            let mc4 := mload(add(mc, 128))
            let mc5 := mload(add(mc, 160))
            let additive := mload(add(mc, 192))

            // read boundary: registers are (value @ final ts) reads, then the PC read (final pc/ts)
            let read_bnd := 1
            let write_bnd := 1
            for { let r := 0 } lt(r, 32) { r := add(r, 1) } {
                let base := mul(r, 12)
                let value := preimage_u32(base)
                let ts_low := preimage_u32(add(base, 4))
                let ts_high := preimage_u32(add(base, 8))
                // read set: Register(0) + mc0*r + mc2*ts_low + mc3*ts_high + mc4*v_low + mc5*v_high + additive
                let c := addmod(mulmod(mc0, r, Pm), additive, Pm)
                c := addmod(c, mulmod(mc2, ts_low, Pm), Pm)
                c := addmod(c, mulmod(mc3, ts_high, Pm), Pm)
                c := addmod(c, mulmod(mc4, and(value, 0xffff), Pm), Pm)
                c := addmod(c, mulmod(mc5, shr(16, value), Pm), Pm)
                read_bnd := mulmod(read_bnd, c, Pm)
                // write set: registers are all "write 0 @ ts 0": Register(0) + mc0*r + additive
                write_bnd := mulmod(write_bnd, addmod(mulmod(mc0, r, Pm), additive, Pm), Pm)
            }
            // PC read: PC(2) + mc4*pc_low + mc5*pc_high + mc2*ts_low + mc3*ts_high + additive
            {
                let pcv := preimage_u32(384)
                // Bind the verified statement to this program's terminal PC.
                if iszero(eq(pcv, EXPECTED_FINAL_PC)) {
                revert(0, 0) }
                let ts_low := preimage_u32(388)
                let ts_high := preimage_u32(392)
                let c := addmod(2, additive, Pm)
                c := addmod(c, mulmod(mc4, and(pcv, 0xffff), Pm), Pm)
                c := addmod(c, mulmod(mc5, shr(16, pcv), Pm), Pm)
                c := addmod(c, mulmod(mc2, ts_low, Pm), Pm)
                c := addmod(c, mulmod(mc3, ts_high, Pm), Pm)
                read_bnd := mulmod(read_bnd, c, Pm)
            }
            // PC write: initial pc=0, initial ts=(4,0) => PC(2) + mc2*4 + additive
            write_bnd := mulmod(write_bnd, addmod(addmod(2, additive, Pm), mulmod(mc2, 4, Pm), Pm), Pm)

            let pp := GKR_PERM_PROD_PTR()
            let read_side := mulmod(mulmod(mload(pp), mload(add(pp, 64)), Pm), read_bnd, Pm)        // read_poly*teardown*read_bnd
            let write_side := mulmod(mulmod(mload(add(pp, 32)), mload(add(pp, 96)), Pm), write_bnd, Pm) // write_poly*init*write_bnd
            if iszero(eq(read_side, write_side)) {
            revert(0, 0) }
        }

        function sumcheck_rounds(ptr, claim, total_rounds) -> next_ptr, next_claim, eq_scale {
            eq_scale := 1
            for { let i := 0 } lt(i, total_rounds) { i := add(i, 1) } {
                let w0 := calldataload(ptr)
                let w1 := calldataload(add(ptr, 32))
                let c0 := shr(128, w0)
                let c1 := and(w0, MASK)
                let c2 := shr(128, w1)
                let c3 := and(w1, MASK)
                let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, mload(P_PTR))
                let r := transcript_4to1_dual(w0, w1) // before-check draw is intentional; see HEURISTICS.md
                // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
                if mod(add(claim, sub(mload(P_PTR), g0g1_scaled)), mload(P_PTR)) {
                revert(0, 0) }
                claim := add(mulmod(add(mulmod(add(mulmod(c3, r, mload(P_PTR)), c2), r, mload(P_PTR)), c1), r, mload(P_PTR)), c0)
                let z := mload(add(POINT_PTR(), mul(i, 32)))
                let zr := mulmod(z, r, mload(P_PTR))
                eq_scale := add(add(add(zr, zr), 1), sub(mul(4, mload(P_PTR)), add(z, r)))
                mstore(add(POINT_PTR(), mul(i, 32)), r)
                ptr := add(ptr, 64)
            }
            next_ptr := ptr
            next_claim := claim
        }



        // Dim-reducing final step for one layer (own frame -> shallow caller stack). Validated
        // in step1_test/GkrCompressYul. `cp` points at the 10 [E;2] LSB lines (sorted). Compute
        // g (products slots 0,1,8,9; lookup num/den pairs (2,3)(4,5)(6,7); running batching powers;
        // boundary permutation on the last layer), check g*eq_scale==claim, absorb the LSB lines,
        // draw r_last + next_batching, interpolate the next claims (sorted order), grow the point.
        function gkr_dr_final(cp, fs, batching, boundary, eq_scale, claim) -> ncp, nbatch {
            let SI := GKR_EQ_PTR() // reuse eq scratch as the sorted-index array (10 slots)
            for { let li := 0 } lt(li, 10) { li := add(li, 1) } {
            mstore(add(SI, mul(li, 32)), li) }
            if boundary {
                mstore(add(SI, 0), 6)
                mstore(add(SI, 32), 7)
                mstore(add(SI, 64), 0)
                mstore(add(SI, 96), 1)
                mstore(add(SI, 128), 2)
                mstore(add(SI, 160), 3)
                mstore(add(SI, 192), 4)
                mstore(add(SI, 224), 5)
                mstore(add(SI, 256), 8)
                mstore(add(SI, 288), 9)
            }
            let g := 0
            let gb := 1
            for { let step := 0 } lt(step, 2) { step := add(step, 1) } {
                let word := calldataload(add(cp, mul(mload(add(SI, mul(step, 32))), 32)))
                g := add(mulmod(gb, mulmod(shr(128, word), and(word, MASK), mload(P_PTR)), mload(P_PTR)), g)
                gb := mulmod(gb, batching, mload(P_PTR))
            }
            for { let pr := 0 } lt(pr, 3) { pr := add(pr, 1) } {
                let wN := calldataload(add(cp, mul(mload(add(SI, mul(add(2, mul(pr, 2)), 32))), 32)))
                let wD := calldataload(add(cp, mul(mload(add(SI, mul(add(3, mul(pr, 2)), 32))), 32)))
                let num := add(mulmod(shr(128, wN), and(wD, MASK), mload(P_PTR)), mulmod(and(wN, MASK), shr(128, wD), mload(P_PTR)))
                let den := mulmod(shr(128, wD), and(wD, MASK), mload(P_PTR))
                g := add(mulmod(gb, num, mload(P_PTR)), g)
                gb := mulmod(gb, batching, mload(P_PTR))
                g := add(mulmod(gb, den, mload(P_PTR)), g)
                gb := mulmod(gb, batching, mload(P_PTR))
            }
            for { let step := 8 } lt(step, 10) { step := add(step, 1) } {
                let word := calldataload(add(cp, mul(mload(add(SI, mul(step, 32))), 32)))
                g := add(mulmod(gb, mulmod(shr(128, word), and(word, MASK), mload(P_PTR)), mload(P_PTR)), g)
                gb := mulmod(gb, batching, mload(P_PTR))
            }
            if mod(add(mulmod(mod(g, mload(P_PTR)), eq_scale, mload(P_PTR)), sub(mload(P_PTR), claim)), mload(P_PTR)) {
            revert(0, 0) }
            // absorb the 320 B of LSB lines (sorted transcript order), draw r_last + next_batching
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            calldatacopy(add(GKR_ABS_PTR(), 32), cp, 320)
            let seed := keccak256(GKR_ABS_PTR(), 352)
            mstore(SEED_PTR(), seed)
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            let r_last := mod(shr(128, seed), mload(P_PTR))
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            nbatch := mod(shr(128, seed), mload(P_PTR))
            mstore(add(POINT_PTR(), mul(fs, 32)), r_last)
            // next claims = interpolate lsb_sorted at r_last (no perm): a + (b-a)*r_last
            for { let li := 0 } lt(li, 10) { li := add(li, 1) } {
                let word := calldataload(add(cp, mul(li, 32)))
                let a := shr(128, word)
                mstore(add(GKR_CLAIMS_PTR(), mul(li, 32)), add(a, mulmod(add(and(word, MASK), sub(mload(P_PTR), a)), r_last, mload(P_PTR))))
            }
            ncp := add(cp, 320)
        }

        // 18 dim-reducing layers (folding_steps 4..21). Reads the 10 claims + batching from
        // gkr_init (GKR_CLAIMS_PTR / GKR_BATCHING_PTR); reuses sumcheck_rounds for the monomial
        // rounds. Validated end-to-end in step1_test/GkrCompressYul (post-state 0xc3616d7d…).
        function gkr_compress(ptr, claim0, alpha0) -> next_ptr, next_claim, next_alpha {
            let batching := mload(GKR_BATCHING_PTR())
            for { let k := 0 } lt(k, 18) { k := add(k, 1) } {
                let fs := add(4, k)
                // initial claim = RLC(claims, batching)
                let claim := 0
                let cb := 1
                for { let c := 0 } lt(c, 10) { c := add(c, 1) } {
                    claim := add(mulmod(cb, mload(add(GKR_CLAIMS_PTR(), mul(c, 32))), mload(P_PTR)), claim)
                    cb := mulmod(cb, batching, mload(P_PTR))
                }
                claim := mod(claim, mload(P_PTR))
                let eq_scale
                ptr, claim,
                eq_scale := sumcheck_rounds(ptr, claim, fs)
                ptr,
                batching := gkr_dr_final(ptr, fs, batching, eq(k, 17), eq_scale, claim)
            }
            mstore(GKR_BATCHING_PTR(), batching)
            next_ptr := ptr
            next_claim := 0
            next_alpha := batching
        }

function sumcheck_circuit_layer3(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl3(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc
            mstore(CIRCUIT_PTR, ptr)
            scl3_caches()
            acc := scl3_g0(alpha, acc)
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }

    
            // WRITEBACK claims for next layer (16 evals)
                for { let wk := 0 } lt(wk, 16) { wk := add(wk, 1) } {
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk)))))
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // split the absorb: final_step, draw, extras). next_claim unused (sccl recomputes).
    next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, 16)
}

            function scl3_caches() {
            }
            function scl3_g0(alpha, a) -> acc { acc := a
    // CopyInExtensionField: [15] = 9
    acc := gate_copyinextensionfield(alpha, acc, 15)
    
    // CopyInExtensionField: [14] = 8
    acc := gate_copyinextensionfield(alpha, acc, 14)
    
    // CopyInExtensionField: [1] = 7
    acc := gate_copyinextensionfield(alpha, acc, 1)
    
    // CopyInExtensionField: [0] = 6
    acc := gate_copyinextensionfield(alpha, acc, 0)
    
    // AggregateLookupRationalPair: [12]/[13] + [10]/[11] = 4/5
    acc := gate_aggregatelookuprationalpair(alpha, acc, 12, 10, 13, 11)
    
    // AggregateLookupRationalPair: [8]/[9] + [6]/[7] = 2/3
    acc := gate_aggregatelookuprationalpair(alpha, acc, 8, 6, 9, 7)
    
    // AggregateLookupRationalPair: [4]/[5] + [2]/[3] = 0/1
    acc := gate_aggregatelookuprationalpair(alpha, acc, 4, 2, 5, 3)
    
            }
            function sccl3(alpha) -> claim {
            let src := GKR_CLAIMS_PTR()
            claim := 0
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 0))))
            }
function sumcheck_circuit_layer2(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl2(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc
            mstore(CIRCUIT_PTR, ptr)
            scl2_caches()
            acc := scl2_g0(alpha, acc)
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }

    
            // WRITEBACK claims for next layer (25 evals)
                for { let wk := 0 } lt(wk, 25) { wk := add(wk, 1) } {
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk)))))
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // split the absorb: final_step, draw, extras). next_claim unused (sccl recomputes).
    next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, 25)
}

            function scl2_caches() {
            }
            function scl2_g0(alpha, a) -> acc { acc := a
    // CopyInExtensionField: [24] = 15
    acc := gate_copyinextensionfield(alpha, acc, 24)
    
    // CopyInExtensionField: [23] = 14
    acc := gate_copyinextensionfield(alpha, acc, 23)
    
    // CopyInExtensionField: [18] = 13
    acc := gate_copyinextensionfield(alpha, acc, 18)
    
    // CopyInExtensionField: [17] = 12
    acc := gate_copyinextensionfield(alpha, acc, 17)
    
    // AggregateLookupRationalPair: [21]/[22] + [19]/[20] = 10/11
    acc := gate_aggregatelookuprationalpair(alpha, acc, 21, 19, 22, 20)
    
    // CopyInExtensionField: [12] = 9
    acc := gate_copyinextensionfield(alpha, acc, 12)
    
    // CopyInExtensionField: [11] = 8
    acc := gate_copyinextensionfield(alpha, acc, 11)
    
    // AggregateLookupRationalPair: [15]/[16] + [13]/[14] = 6/7
    acc := gate_aggregatelookuprationalpair(alpha, acc, 15, 13, 16, 14)
    
    // AggregateLookupRationalPair: [5]/[6] + [3]/[4] = 4/5
    acc := gate_aggregatelookuprationalpair(alpha, acc, 5, 3, 6, 4)
    
    // AggregateLookupRationalPair: [9]/[10] + [7]/[8] = 2/3
    acc := gate_aggregatelookuprationalpair(alpha, acc, 9, 7, 10, 8)
    
    // MaskIntoIdentityProduct: [2]*[0] + (1-[0]) = 1
    acc := gate_maskintoidentityproduct(alpha, acc, 2, 0)
    
    // MaskIntoIdentityProduct: [1]*[0] + (1-[0]) = 0
    acc := gate_maskintoidentityproduct(alpha, acc, 1, 0)
    
            }
            function sccl2(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := 0
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 15))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 14))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 13))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 12))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 11))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 10))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 0))))
            }
function sumcheck_circuit_layer1(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl1(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc
            mstore(CIRCUIT_PTR, ptr)
            scl1_caches()
            acc := scl1_g0(alpha, acc)
            acc := scl1_g1(alpha, acc)
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }

    
            // WRITEBACK claims for next layer (72 evals)
                for { let wk := 0 } lt(wk, 72) { wk := add(wk, 1) } {
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk)))))
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // split the absorb: final_step, draw, extras). next_claim unused (sccl recomputes).
    {
            let base := mload(CIRCUIT_PTR)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            let bp := add(GKR_ABS_PTR(), 32)
            calldatacopy(bp, add(base, mul(16, 0)), mul(16, 8))
            bp := add(bp, mul(16, 8))
            calldatacopy(bp, add(base, mul(16, 48)), mul(16, 24))
            bp := add(bp, mul(16, 24))
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)))))
            bp := add(bp, 16)
            let s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR()))
            mstore(SEED_PTR(), s)
            s := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), s)
            next_alpha := mod(shr(128, s), P)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            bp := add(GKR_ABS_PTR(), 32)
            calldatacopy(bp, add(base, mul(16, 8)), mul(16, 40))
            bp := add(bp, mul(16, 40))
            s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR()))
            mstore(SEED_PTR(), s)
            next_ptr := add(ptr, mul(16, 72))
            next_claim := 0
            }
}

            function scl1_caches() {
    {  // VectorizedLookup: (0 + 1[9]) + (0 + 1[10]) + (0 + 1[11]) + (0 + 0) + (0 + 0) + (0 + 0) + (0 + 0) + (0 + 0) + (0 + 0) + (0 + 1[8]) = Cache(0)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))))), add(0, 0)), add(0, 0)), add(0, 0)), add(0, 0)), add(0, 0)), add(0, 0)), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)), mod(gate, P))
    }
    {  // VectorizedLookup: (0 + 1[13]) + (0 + 1[14]) + (0 + 1[15]) + (0 + 1[16]) + (0 + 1[17]) + (0 + 1[18]) + (0 + 1[19]) + (0 + 1[20]) + (0 + 0) + (0 + 1[12]) = Cache(1)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 12)))))), add(0, 0)), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 15)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 14)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 13))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)), mod(gate, P))
    }
    {  // VectorizedLookup: (0 + 1[22]) + (0 + 1[23]) + (0 + 1[24]) + (0 + 1[25]) + (0 + 1[26]) + (0 + 1[27]) + (0 + 1[28]) + (0 + 1[29]) + (0 + 0) + (0 + 1[21]) = Cache(2)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))))), add(0, 0)), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 29)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)), mod(gate, P))
    }
    {  // VectorizedLookup: (0 + 1[31]) + (0 + 1[32]) + (0 + 1[33]) + (0 + 1[34]) + (0 + 1[35]) + (0 + 1[36]) + (0 + 1[37]) + (0 + 1[38]) + (0 + 0) + (0 + 1[30]) = Cache(3)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 30)))))), add(0, 0)), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 38)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 37)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 36)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 35)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 34)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 33)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 32)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 31))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)), mod(gate, P))
    }
    {  // VectorizedLookup: (0 + 1[40]) + (0 + 1[41]) + (0 + 1[42]) + (0 + 1[43]) + (0 + 1[44]) + (0 + 1[45]) + (0 + 1[46]) + (0 + 1[47]) + (0 + 0) + (0 + 1[39]) = Cache(4)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 39)))))), add(0, 0)), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)), mod(gate, P))
    }
            }
            function scl1_g0(alpha, a) -> acc { acc := a
    // CopyInExtensionField: [5] = 24
    acc := gate_copyinextensionfield(alpha, acc, 5)
    
    // CopyInExtensionField: [6] = 23
    acc := gate_copyinextensionfield(alpha, acc, 6)
    
    {  // LookupUnbalancedPairWithMaterializedVectorInputs: [70]/[71] + 1/(δ + Cache(4)) = 21/22
        let den_out := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedVectorInputs: 1/(δ+Cache(2)) + 1/(δ+Cache(3)) = 19/20
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedVectorInputs: 1/(δ+Cache(0)) + 1/(δ+Cache(1)) = 17/18
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    // CopyInExtensionField: [62] = 16
    acc := gate_copyinextensionfield(alpha, acc, 62)
    
    // CopyInExtensionField: [61] = 15
    acc := gate_copyinextensionfield(alpha, acc, 61)
    
    // AggregateLookupRationalPair: [65]/[66] + [63]/[64] = 13/14
    acc := gate_aggregatelookuprationalpair(alpha, acc, 65, 63, 66, 64)
    
    {  // LookupUnbalancedPairWithMaterializedBaseInputs: [67]/[68] + 1/(δ + [69]) = 11/12
        let den_out := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69))))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupUnbalancedPairWithMaterializedBaseInputs: [48]/[49] + 1/(δ + [7]) = 9/10
        let den_out := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7))))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    // AggregateLookupRationalPair: [52]/[53] + [50]/[51] = 7/8
    acc := gate_aggregatelookuprationalpair(alpha, acc, 52, 50, 53, 51)
    
    // AggregateLookupRationalPair: [56]/[57] + [54]/[55] = 5/6
    acc := gate_aggregatelookuprationalpair(alpha, acc, 56, 54, 57, 55)
    
            }
            function scl1_g1(alpha, a) -> acc { acc := a
    {  // LookupUnbalancedPairWithMaterializedBaseInputs: [58]/[59] + 1/(δ + [60]) = 3/4
        let den_out := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60))))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // TrivialProduct: [2]*[4] = 2
        let gate := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 4)))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // TrivialProduct: [1]*[3] = 1
        let gate := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 1)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInBaseField: [0] = 0
        let gate := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 0))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function sccl1(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := 0
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 24))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 23))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 22))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 21))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 20))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 19))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 18))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 17))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 16))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 15))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 14))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 13))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 12))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 11))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 10))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 0))))
            }
function sumcheck_circuit_layer0(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl0(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc
            mstore(CIRCUIT_PTR, ptr)
            scl0_caches()
            acc := scl0_g0(alpha, acc)
            acc := scl0_g1(alpha, acc)
            acc := scl0_g2(alpha, acc)
            acc := scl0_g3(alpha, acc)
            acc := scl0_g4(alpha, acc)
            acc := scl0_g5(alpha, acc)
            acc := scl0_g6(alpha, acc)
            acc := scl0_g7(alpha, acc)
            acc := scl0_g8(alpha, acc)
            acc := scl0_g9(alpha, acc)
            acc := scl0_g10(alpha, acc)
            acc := scl0_g11(alpha, acc)
            acc := scl0_g12(alpha, acc)
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }

    
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // split the absorb: final_step, draw, extras). next_claim unused (sccl recomputes).
    {
            let base := mload(CIRCUIT_PTR)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            let bp := add(GKR_ABS_PTR(), 32)
            calldatacopy(bp, add(base, mul(16, 38)), mul(16, 66))
            bp := add(bp, mul(16, 66))
            calldatacopy(bp, add(base, mul(16, 2)), mul(16, 2))
            bp := add(bp, mul(16, 2))
            calldatacopy(bp, add(base, mul(16, 5)), mul(16, 7))
            bp := add(bp, mul(16, 7))
            calldatacopy(bp, add(base, mul(16, 14)), mul(16, 24))
            bp := add(bp, mul(16, 24))
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 5)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 6)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 7)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 8)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 9)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 10)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 11)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 12)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 13)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 14)))))
            bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 15)))))
            bp := add(bp, 16)
            let s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR()))
            mstore(SEED_PTR(), s)
            s := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), s)
            next_alpha := mod(shr(128, s), P)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            bp := add(GKR_ABS_PTR(), 32)
            calldatacopy(bp, add(base, mul(16, 0)), mul(16, 2))
            bp := add(bp, mul(16, 2))
            calldatacopy(bp, add(base, mul(16, 4)), mul(16, 1))
            bp := add(bp, mul(16, 1))
            calldatacopy(bp, add(base, mul(16, 12)), mul(16, 2))
            bp := add(bp, mul(16, 2))
            calldatacopy(bp, add(base, mul(16, 104)), mul(16, 10))
            bp := add(bp, mul(16, 10))
            s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR()))
            mstore(SEED_PTR(), s)
            next_ptr := add(ptr, mul(16, 114))
            next_claim := 0
            }
}

            function scl0_caches() {
    {  // MemoryTuple: (γ + 0 + α[4] + α²0 + α³(0 + [0]) + α⁴[1] + α⁵[2] + α⁶[3]) = Cache(0)
        let gate := add(gkr_memrel_compress_low(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 4)))), 0), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 0))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 1)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + [9] + α[10] + α²[11] + α³(0 + [5]) + α⁴[6] + α⁵[7] + α⁶[8]) = Cache(1)
        let gate := add(gkr_memrel_compress_low(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11))))), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 5))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 6)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + 0 + α[4] + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[2] + α⁶[3]) = Cache(2)
        let gate := add(gkr_memrel_compress_low(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 4)))), 0), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + [9] + α[10] + α²[11] + α³(1 + [24]) + α⁴[25] + α⁵[7] + α⁶[8]) = Cache(3)
        let gate := add(gkr_memrel_compress_low(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11))))), gkr_memrel_compress_high(add(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + [16] + α[17] + α²[18] + α³(0 + [12]) + α⁴[13] + α⁵[14] + α⁶[15]) = Cache(4)
        let gate := add(gkr_memrel_compress_low(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18))))), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 12))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 13)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 14)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 15))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + 2 + α0 + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[22] + α⁶[23]) = Cache(5)
        let gate := add(gkr_memrel_compress_low(2, 0, 0), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 5)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + [16] + α[17] + α²[18] + α³(2 + [24]) + α⁴[25] + α⁵[19] + α⁶[20]) = Cache(6)
        let gate := add(gkr_memrel_compress_low(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18))))), gkr_memrel_compress_high(add(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 6)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + 2 + α0 + α²0 + α³(0 + [28]) + α⁴[29] + α⁵[26] + α⁶[27]) = Cache(7)
        let gate := add(gkr_memrel_compress_low(2, 0, 0), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 29)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 7)), mod(gate, P))
    }
    {  // SingleColumnLookup: 0 + -1[24] + 1[0] + 2^19[98] = Cache(8)
        let gate := add(0, add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 0))))), mulmod(524288, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 98)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 8)), mod(gate, P))
    }
    {  // SingleColumnLookup: 2^19 + -1[25] + 1[1] + -1[98] = Cache(9)
        let gate := add(524288, add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 1))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 98)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 9)), mod(gate, P))
    }
    {  // SingleColumnLookup: -1 + -1[24] + 1[5] + 2^19[99] = Cache(10)
        let gate := add(sub(P, 1), add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 5))))), mulmod(524288, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 99)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 10)), mod(gate, P))
    }
    {  // SingleColumnLookup: 2^19 + -1[25] + 1[6] + -1[99] = Cache(11)
        let gate := add(524288, add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 6))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 99)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 11)), mod(gate, P))
    }
    {  // SingleColumnLookup: -2 + -1[24] + 1[12] + 2^19[100] = Cache(12)
        let gate := add(sub(P, 2), add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 12))))), mulmod(524288, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 100)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 12)), mod(gate, P))
    }
    {  // SingleColumnLookup: 2^19 + -1[25] + 1[13] + -1[100] = Cache(13)
        let gate := add(524288, add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 13))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 100)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 13)), mod(gate, P))
    }
    {  // VectorizedLookup: (0 + 1[22]) + (0 + 1[23]) + (0 + 1[4]) + (0 + 1[38]) + (0 + 1[39]) + (0 + 1[40]) + (0 + 1[41]) + (0 + 1[42]) + (0 + 1[43] + 2[44] + 2^2[45] + 2^3[46] + 2^4[47] + 2^5[48] + 2^6[49] + 2^7[50] + 2^8[51] + 2^9[52] + 2^10[53] + 2^11[54] + 2^12[55] + 2^13[56] + 2^14[57] + 2^15[58] + 2^16[59] + 2^17[9] + 2^18[16]) + (46 + 0) = Cache(14)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(46, 0)), add(0, add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), P)), mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), P)), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P)), mulmod(16, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P)), mulmod(32, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), P)), mulmod(64, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), P)), mulmod(128, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), P)), mulmod(512, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), P)), mulmod(1024, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P)), mulmod(2048, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(4096, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(8192, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(16384, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P)), mulmod(32768, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P)), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P)), mulmod(131072, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P)), mulmod(262144, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 39)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 38)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 4)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 14)), mod(gate, P))
    }
    {  // VectorizedLookupSetup: β⁰[104] + β¹[105] + β²[106] + β³[107] + β⁴[108] + β⁵[109] + β⁶[110] + β⁷[111] + β⁸[112] + β⁹[113] = Cache(15)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 113))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 112))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 111))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 110))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 109))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 108))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 107))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 106))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 105))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 104)))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 15)), mod(gate, P))
    }
    {  // RangeCheck16Bits: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8])(1 - r[7])(1 - r[6])(1 - r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = Cache(16)
        let gate := gkr_virtual_poly_rangecheck(16)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)), mod(gate, P))
    }
    {  // RangeCheckTimestamp: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8] + 2^16 r[7] + 2^17 r[6] + 2^18 r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = Cache(17)
        let gate := gkr_virtual_poly_rangecheck(19)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)), mod(gate, P))
    }
    {  // InitsAndTeardownsLow: 4(2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10]) = Cache(18)
        let gate := mul(4, gkr_virtual_poly_compose_vars(14, 0)) // u32 word-aligned
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18)), mod(gate, P))
    }
    {  // InitsAndTeardownsHigh: 2^0 r[9] + 2^1 r[8] + 2^2 r[7] + 2^3 r[6] + 2^4 r[5] + 2^5 r[4] + 2^6 r[3] + 2^7 r[2] + 2^8 r[1] + 2^9 r[0] = Cache(19)
        let gate := gkr_virtual_poly_compose_vars(8, 14)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19)), mod(gate, P))
    }
            }
            function scl0_g0(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[100] + [100](1[100])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 100)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 100)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 100)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[99] + [99](1[99])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 99)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 99)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 99)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[98] + [98](1[98])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 98)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 98)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 98)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[97] + [97](1[97])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[96] + [96](1[96])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[95] + [95](1[95])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[94] + [94](1[94])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[93] + [93](1[93])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[92] + [92](1[92])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[91] + [91](1[91])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[64] + [64](1[64])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[63] + [63](1[63])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g1(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[62] + [62](1[62])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[61] + [61](1[61])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[60] + [60](1[60])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[16] + [16](1[16])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[9] + [9](1[9])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[59] + [59](1[59])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[58] + [58](1[58])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[57] + [57](1[57])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[56] + [56](1[56])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[55] + [55](1[55])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[54] + [54](1[54])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[53] + [53](1[53])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g2(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[52] + [52](1[52])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[51] + [51](1[51])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[50] + [50](1[50])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[49] + [49](1[49])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[48] + [48](1[48])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[47] + [47](1[47])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[46] + [46](1[46])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[45] + [45](1[45])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[44] + [44](1[44])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[43] + [43](1[43])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0x380000000000000000000000000 + 0xe0000000000000000000000000[24] + -1[25] + 0x6ffff20000000000000000000000001[28] + 1[29] + 0
        let gate := add(add(0x380000000000000000000000000, add(add(add(mulmod(0xe0000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), P)), mulmod(0x6ffff20000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 29)))))), 0)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0x37ffe4000000000000000000000 + 0xdfff2000000000000000000000[24] + 0x6ffff2000e000000000000000000001[28] + [24](0x6ffffffffe400000000000000000001[24] + 0x3800000000000000000000[28]) + [28](0x6ffffffffe400000000000000000001[28])
        let gate := add(add(0x37ffe4000000000000000000000, add(mulmod(0xdfff2000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P), mulmod(0x6ffff2000e000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))), P))), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), add(mulmod(0x6ffffffffe400000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P), mulmod(0x3800000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))), mulmod(0x6ffffffffe400000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g3(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[43] + 1[44] + 1[45] + 1[46] + 1[47] + 1[48] + 1[49] + 1[50] + 1[51] + 1[52] + 1[53] + 1[54] + 1[55] + 1[56] + 1[57] + 1[58] + 1[59] + 1[9] + 1[16] + [43](-1[21]) + [44](-1[21]) + [45](-1[21]) + [46](-1[21]) + [47](-1[21]) + [48](-1[21]) + [49](-1[21]) + [50](-1[21]) + [51](-1[21]) + [52](-1[21]) + [53](-1[21]) + [54](-1[21]) + [55](-1[21]) + [56](-1[21]) + [57](-1[21]) + [58](-1[21]) + [59](-1[21]) + [9](-1[21]) + [16](-1[21])
        let gate := add(add(0, add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))))), add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[97] + [43](-1[21]) + [44](-1[21]) + [45](-1[21]) + [46](-1[21]) + [47](-1[21]) + [48](-1[21]) + [49](-1[21]) + [50](-1[21]) + [51](-1[21]) + [52](-1[21]) + [53](-1[21]) + [54](-1[21]) + [55](-1[21]) + [56](-1[21]) + [58](-1[21]) + [59](-1[21]) + [9](-1[21]) + [16](-1[21])
        let gate := add(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97))))), add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [95](1[96]) + [96](1[23] + -1[27])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 2^2[96] + [95](-2^16[96]) + [96](1[22] + -1[26])
        let gate := add(add(0, mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), P)), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[96] + -1[21] + [53](1[21]) + [54](1[21]) + [55](1[21]) + [56](1[21])
        let gate := add(add(0, add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P))), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [63](1[16]) + [64](1[16])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [63](1[16]) + [64](2[16]) + [86](2^2[16]) + [16](-1[17])
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86)))), mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [94](1[8] + -1[20]) + [8](-1[9] + -1[16]) + [9](1[20]) + [16](1[20])
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [94](1[7] + -1[19]) + [7](-1[9] + -1[16]) + [9](1[19]) + [16](1[19])
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[94] + [62](-1[9])
        let gate := add(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94))))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [62](1[16])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [62](1[16])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g4(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [66](1[16]) + [16](-1[18])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [66](1[9]) + [9](-1[11])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [65](1[16]) + [16](-1[17])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [65](1[9]) + [9](-1[10])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [41](1[9] + 1[16]) + [60](1[9] + 1[16]) + [61](-2^16[9] + -2^16[16]) + [3](1[9] + 1[16]) + [9](-1[11]) + [16](-1[18])
        let gate := add(add(0, 0), add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16))))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [40](1[9] + 1[16]) + [60](-2^16[9] + -2^16[16]) + [2](1[9] + 1[16]) + [9](-1[10]) + [16](-1[17])
        let gate := add(add(0, 0), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16))))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[18] + [16](-1[18])
        let gate := add(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18))))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[39] + 1[17] + [39](1[16]) + [16](-1[17])
        let gate := add(add(0, add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 39)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))))), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 39)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[11] + [9](-1[11])
        let gate := add(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11))))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[38] + 1[10] + [38](1[9]) + [9](-1[10])
        let gate := add(add(0, add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 38)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))))), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 38)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [58](1[68] + 2^8[69] + 1[72] + 2^8[73] + 1[76] + 2^8[77] + 1[80] + 2^8[81] + -1[20]) + [59](1[68] + 2^8[69] + 1[71] + 2^8[72] + 1[74] + 2^8[75] + 2^8[78] + 1[81] + -1[20])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(add(add(add(add(add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 72))))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 73)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 76))))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 77)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 80))))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 81)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(add(add(add(add(add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71))))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 72)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 74))))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 75)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 78)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 81))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [58](1[66] + 2^8[67] + 1[70] + 2^8[71] + 1[74] + 2^8[75] + 1[78] + 2^8[79] + -1[19]) + [59](1[66] + 2^8[67] + 2^8[70] + 1[73] + 1[76] + 2^8[77] + 1[79] + 2^8[80] + -1[19])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(add(add(add(add(add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70))))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 74))))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 75)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 78))))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 79)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(add(add(add(add(add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 73))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 76))))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 77)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 79))))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 80)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g5(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [93](1[20])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [93](1[19])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [92](1[20])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [87](1[91]) + [91](-1[20])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [67](1[92]) + [86](1[91]) + [91](-1[19]) + [92](-1[19])
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[93] + [53](-1[57]) + [54](-1[57]) + [55](-1[57]) + [56](-1[57])
        let gate := add(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93))))), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[55] + 1[92] + [55](1[57])
        let gate := add(add(0, add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[53] + -1[54] + 1[91] + [53](1[57]) + [54](1[57])
        let gate := add(add(0, add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))))), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [53](1[64]) + [54](1[64]) + [64](1[90])
        let gate := add(add(0, 0), add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [41](1[53] + 1[54] + 1[90]) + [53](1[62] + -2^16[63] + 1[23] + -1[27]) + [54](1[62] + -2^16[63] + 1[3] + -1[27]) + [55](1[62] + -2^16[63] + 1[23] + -1[27]) + [56](1[62] + -2^16[63] + 1[23] + -1[27])
        let gate := add(add(0, 0), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90))))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 2^2[55] + 2^2[56] + -2^2[90] + [40](1[53] + 1[54] + 1[90]) + [53](-2^16[62] + -1[89] + 1[22]) + [54](-2^16[62] + -1[89] + 1[2]) + [55](-2^16[62] + -1[89] + 1[22]) + [56](-2^16[62] + -1[89] + 1[22])
        let gate := add(add(0, add(add(mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P), mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(sub(P, 4), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90)))), P))), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90))))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 89)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 89)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 89)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 89)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22))))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[90] + [56](1[67])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g6(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [41](-1[55]) + [53](1[68] + -1[8]) + [54](1[68] + -1[8]) + [55](1[68] + -1[8]) + [56](1[68] + -1[8])
        let gate := add(add(0, 0), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [41](1[55]) + [53](1[60] + -2^16[61] + -1[87] + 1[23]) + [54](1[60] + -2^16[61] + -1[87] + 1[23]) + [55](1[60] + -2^16[61] + 1[87] + -1[3] + 1[8]) + [56](1[60] + -2^16[61] + 1[87] + -1[3] + 1[8])
        let gate := add(add(0, 0), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8))))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 2^2[53] + 2^2[54] + [40](1[55]) + [53](-2^16[60] + -1[86] + 1[22]) + [54](-2^16[60] + -1[86] + 1[22]) + [55](-2^16[60] + 1[86] + -1[2] + 1[7]) + [56](-2^16[60] + 1[86] + -1[2] + 1[7])
        let gate := add(add(0, add(mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P))), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7))))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [50](1[20])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [50](1[19])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [50](1[6])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 6)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [50](1[5])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 5)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [50](1[8])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [50](1[7])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 65535[46] + 65535[47] + 65535[48] + 65535[49] + [41](1[43] + 1[45]) + [43](-2^16[60] + 1[61] + 1[3] + 1[8] + -1[20]) + [44](-2^16[60] + 1[61] + -1[3] + 1[8] + 1[20]) + [45](-2^16[60] + 1[61] + -1[20] + 1[23]) + [46](-2^16[60] + 1[61] + 1[87] + -1[20]) + [47](-2^16[60] + 1[61] + 1[87] + -1[20]) + [48](-2^16[60] + 1[61] + 1[87] + -1[20]) + [49](-2^16[60] + 1[61] + 1[87] + -1[20]) + [52](-2^16[60] + 1[61] + 1[62] + -2^16[63] + 1[3] + 1[8] + 1[15] + -1[20])
        let gate := add(add(0, add(add(add(mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P), mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P)), mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), P)), mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), P))), add(add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45))))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), add(add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), add(add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), add(add(add(add(add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62))))), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 15))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 65535[46] + 65535[47] + 65535[48] + 65535[49] + [40](1[43] + 1[45]) + [43](-2^16[61] + 1[2] + 1[7] + -1[19]) + [44](-2^16[61] + -1[2] + 1[7] + 1[19]) + [45](-2^16[61] + -1[19] + 1[22]) + [46](-2^16[61] + 1[86] + -1[19]) + [47](-2^16[61] + 1[86] + -1[19]) + [48](-2^16[61] + 1[86] + -1[19]) + [49](-2^16[61] + 1[86] + -1[19]) + [52](-2^16[61] + -2^16[62] + 1[2] + 1[7] + 1[14] + -1[19])
        let gate := add(add(0, add(add(add(mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P), mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P)), mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), P)), mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), P))), add(add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45))))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), add(add(add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 14))))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[46] + 1[47] + 1[48] + 1[49] + [46](-1[60]) + [47](-1[60]) + [48](-1[60]) + [49](-1[60])
        let gate := add(add(0, add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))))), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g7(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [46](-1[2] + -2^16[3] + -1[7] + -2^16[8] + 1[19] + 2^16[20]) + [47](-1[2] + -2^16[3] + 1[7] + 2^16[8] + 1[19] + 2^16[20]) + [48](-1[88] + 1[19] + 2^16[20]) + [49](-1[88] + 1[19] + 2^16[20])
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), add(add(add(add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19))))), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), add(add(add(add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7))))), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19))))), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19))))), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19))))), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[21] + [21](1[21])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupWithCachedDensAndSetup: (([21])·((Cache(15))+δ) − ([103])·((Cache(14))+δ)) / (((Cache(14))+δ)((Cache(15))+δ)) = 70/71
        let bg := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 14))))
        let dg := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 15))))
        let den_out := mulmod(bg, dg, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), dg, P), sub(mul(2, P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 103)))), bg, P)))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInBaseField: Cache(13) = 69
        let gate := mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 13)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+Cache(11)) + 1/(δ+Cache(12)) = 67/68
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 11))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 12))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+Cache(9)) + 1/(δ+Cache(10)) = 65/66
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 9))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 10))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[29]) + 1/(δ+Cache(8)) = 63/64
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 29)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 8))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupFromMaterializedBaseInputWithSetup: 1/(δ + [28]) - [102]/(δ + Cache(17)) = 61/62
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28))))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)))), sub(P, mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 102)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28))))), P)))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInBaseField: [27] = 60
        let gate := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[18]) + 1/(δ+[26]) = 58/59
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[11]) + 1/(δ+[17]) = 56/57
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[89]) + 1/(δ+[10]) = 54/55
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 89)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g8(alpha, a) -> acc { acc := a
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[20]) + 1/(δ+[23]) = 52/53
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[87]) + 1/(δ+[19]) = 50/51
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupFromMaterializedBaseInputWithSetup: 1/(δ + [86]) - [101]/(δ + Cache(16)) = 48/49
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86))))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)))), sub(P, mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 101)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86))))), P)))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[81]) = 47
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 81)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[80]) = 46
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 80)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[79]) + [59](1[81]) = 45
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 79)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 81)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[78]) + [59](1[80]) = 44
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 78)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 80)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [42](1[58]) + [59](1[79]) = 43
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 79)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [40](1[58]) + [53](1[26]) + [54](1[26]) + [55](1[26]) + [56](1[26]) + [58](1[65]) + [59](1[78]) = 42
        let gate := add(add(0, 0), add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 78)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [53](1[64]) + [54](1[64]) + [55](1[64]) + [56](1[64]) + [58](0x70000000000000000000000000000[83] + 0x6f90000000000000000000000000001[3]) + [59](1[65] + 0x70000000000000000000000000000[85] + 0x6f90000000000000000000000000001[8]) = 41
        let gate := add(add(0, 0), add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 83)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 85)))), P)), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 3[58] + [53](1[89]) + [54](1[89]) + [55](1[89]) + [56](1[89]) + [59](0x70000000000000000000000000000[83] + 0x6f90000000000000000000000000001[3]) = 40
        let gate := add(add(0, mulmod(3, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P)), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 89)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 89)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 89)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 89)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 83)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 2[53] + 2[54] + 2[55] + 2[56] + 9[58] + [42](1[59]) = 39
        let gate := add(add(0, add(add(add(add(mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(9, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g9(alpha, a) -> acc { acc := a
    {  // MaxQuadratic: 0 + 0 + [58](1[77]) = 38
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 77)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[76]) = 37
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 76)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[75]) + [59](1[77]) = 36
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 75)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 77)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[74]) + [59](1[76]) = 35
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 74)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 76)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [42](1[58]) + [59](1[75]) = 34
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 75)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [40](1[58]) + [58](1[65]) + [59](1[74]) = 33
        let gate := add(add(0, 0), add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 74)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [53](1[67]) + [54](1[67]) + [55](1[67]) + [56](1[67]) + [58](1[83]) + [59](1[65] + 1[85]) = 32
        let gate := add(add(0, 0), add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 83)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 85))))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 2[58] + [42](2^4[53] + 2^4[54] + 2^4[55] + 2^4[56]) + [53](2^2[61] + 2^3[65] + 2[66] + 1[69]) + [54](2^2[61] + 2^3[65] + 2[66] + 1[69]) + [55](2^2[61] + 2^3[65] + 2[66] + 1[69]) + [56](2^2[61] + 2^3[65] + 2[66] + 1[69]) + [59](1[83]) = 31
        let gate := add(add(0, mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P)), add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), add(add(add(mulmod(16, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(16, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(16, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(16, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(add(add(mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(add(add(mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(add(add(mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(add(add(mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 83)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 51[53] + 51[54] + 51[55] + 51[56] + 9[58] + [42](1[59]) = 30
        let gate := add(add(0, add(add(add(add(mulmod(51, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(51, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(51, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(51, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(9, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[73]) = 29
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 73)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[72]) = 28
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 72)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[71]) + [59](1[73]) = 27
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 73)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g10(alpha, a) -> acc { acc := a
    {  // MaxQuadratic: 0 + 0 + [58](1[70]) + [59](1[72]) = 26
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 72)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [42](1[58]) + [59](1[71]) = 25
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [40](1[58]) + [58](1[65]) + [59](1[70]) = 24
        let gate := add(add(0, 0), add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [41](1[59]) + [53](1[69]) + [54](1[69]) + [55](1[69]) + [56](1[69]) + [58](0x70000000000000000000000000000[82] + 0x6f90000000000000000000000000001[2]) + [59](0x70000000000000000000000000000[84] + 0x6f90000000000000000000000000001[7]) = 23
        let gate := add(add(0, 0), add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 82)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 84)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 1[58] + [53](1[68]) + [54](1[68]) + [55](1[68]) + [56](1[68]) + [59](0x70000000000000000000000000000[82] + 0x6f90000000000000000000000000001[2]) = 22
        let gate := add(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58))))), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 82)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 5[53] + 5[54] + 5[55] + 5[56] + 9[58] + [42](1[59]) = 21
        let gate := add(add(0, add(add(add(add(mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(9, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[69]) = 20
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[68]) = 19
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[67]) + [59](1[69]) = 18
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[66]) + [59](1[68]) = 17
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [42](1[58]) + [59](1[67]) = 16
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [40](1[58]) + [58](1[65]) + [59](1[66]) = 15
        let gate := add(add(0, 0), add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g11(alpha, a) -> acc { acc := a
    {  // MaxQuadratic: 0 + 0 + [40](1[59]) + [53](1[66]) + [54](1[66]) + [55](1[66]) + [56](1[66]) + [58](1[82]) + [59](1[84]) = 14
        let gate := add(add(0, 0), add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 82)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 84)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [53](1[3]) + [54](1[3]) + [55](1[3]) + [56](1[3]) + [59](1[82]) = 13
        let gate := add(add(0, 0), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 82)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 5[53] + 5[54] + 5[55] + 5[56] + 9[58] + [42](1[59]) = 12
        let gate := add(add(0, add(add(add(add(mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(9, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[65]) + [20](1[94]) = 11
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [53](1[65]) + [54](1[65]) + [55](1[65]) + [56](1[65]) + [58](0x70000000000000000000000000000[84] + 0x6f90000000000000000000000000001[7]) + [59](1[65]) + [19](1[94]) = 10
        let gate := add(add(0, 0), add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 84)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [41](1[59]) + [53](1[86] + 1[87]) + [54](1[86] + 1[87]) + [55](1[86] + 1[87]) + [56](1[86] + 1[87]) + [58](1[84]) + [65](1[94]) + [66](2^16[94]) = 9
        let gate := add(add(0, 0), add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87))))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 84)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 1[53] + 1[54] + 1[55] + 1[56] + 2^3[58] + 3[59] + [21](34[94]) = 8
        let gate := add(add(0, add(add(add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56))))), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P)), mulmod(3, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), mulmod(34, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + -2^6[9] + -2^6[16] + [9](2^16[62] + 1[66]) + [16](2^16[62] + 1[66]) = 7
        let gate := add(add(0, add(mulmod(sub(P, 64), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(sub(P, 64), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P))), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), add(mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66))))), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), add(mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66))))), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[0]<<8)) + α³[32] + α⁴[33] + α⁵[30] + α⁶[31]) * (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[1]<<8)) + α³[36] + α⁴[37] + α⁵[34] + α⁶[35]) = 6
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR(), mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))), P))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(8, gkr_inits_teardowns_topbits(396))), P), gkr_memrel_compress_high(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 32)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 33)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 30)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 31))))))) // for memrel we collect
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(8, gkr_inits_teardowns_topbits(400))), P), gkr_memrel_compress_high(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 36)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 37)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 34)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 35))))))) // for memrel we collect
        let gate := mulmod(lhs, rhs, P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[0]<<8)) + 0) * (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[1]<<8)) + 0) = 5
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR(), mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))), P))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(8, gkr_inits_teardowns_topbits(396))), P), 0)) // for memrel we collect
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(8, gkr_inits_teardowns_topbits(400))), P), 0)) // for memrel we collect
        let gate := mulmod(lhs, rhs, P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductFromCaches: Cache(6)*Cache(7) = 4
        let gate := mulmod(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 6))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 7))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductFromCaches: Cache(4)*Cache(5) = 3
        let gate := mulmod(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 5))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g12(alpha, a) -> acc { acc := a
    {  // InitialGrandProductFromCaches: Cache(2)*Cache(3) = 2
        let gate := mulmod(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductFromCaches: Cache(0)*Cache(1) = 1
        let gate := mulmod(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInBaseField: [21] = 0
        let gate := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function sccl0(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := 0
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 71))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 70))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 69))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 68))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 67))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 66))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 65))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 64))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 63))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 62))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 61))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 60))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 59))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 58))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 57))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 56))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 55))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 54))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 53))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 52))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 51))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 50))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 49))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 48))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 47))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 46))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 45))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 44))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 43))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 42))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 41))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 40))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 39))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 38))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 37))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 36))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 35))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 34))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 33))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 32))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 31))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 30))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 29))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 28))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 27))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 26))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 25))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 24))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 23))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 22))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 21))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 20))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 19))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 18))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 17))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 16))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 15))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 14))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 13))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 12))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 11))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 10))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 0))))
            }
function sumcheck_rounds_circuit(ptr, claim) -> next_ptr, next_claim, eq_scale {
    // NB: need to inline GKR_CIRCUIT_LAYER_ROUNDS unfortunately
    eq_scale := 1
    for { let i := 0 } lt(i, GKR_CIRCUIT_LAYER_ROUNDS) { i := add(i, 1) } {
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
        if mod(add(claim, sub(P, g0g1_scaled)), P) { revert(0, 0) }

        claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
        let z := mload(add(POINT_PTR(), mul(i, 32)))
        let zr := mulmod(z, r, P)
        eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
        mstore(add(POINT_PTR(), mul(i, 32)), r)
        ptr := add(ptr, 64)
    }
    next_ptr := ptr
    next_claim := claim
}
function transcriptNto1(ptr, input_elements) -> alpha {
    let input_bytes := mul(input_elements, 16)
    calldatacopy(add(SEED_PTR(), 32), ptr, input_bytes)
    let seed := keccak256(SEED_PTR(), add(32, input_bytes)) // absorb evals
    mstore(SEED_PTR(), seed)
    seed := keccak256(SEED_PTR(), 32)                       // draw (the mirror draws a fresh el)
    mstore(SEED_PTR(), seed)
    alpha := mod(shr(128, seed), P)                         // batching is a field element mod P
}
function sumcheck_claims_batch(ptr, points) -> next_ptr, next_claim, next_alpha {
    let is_odd := mod(points, 2)
    if is_odd {
        next_claim := shr(128, calldataload(add(ptr, mul(16, sub(points, 1)))))
    }
    next_alpha := transcriptNto1(ptr, points)
    let even_points := sub(points, is_odd)
    let pairs := shr(1, even_points)
    for { let pair := sub(pairs, 1) } lt(pair, pairs) { pair := sub(pair, 1) } {
        let word := calldataload(add(ptr, mul(pair, 32)))
        let el1 := and(MASK, word)
        let el0 := shr(128, word)
        next_claim := add(mulmod(next_claim, next_alpha, P), el1)
        next_claim := add(mulmod(next_claim, next_alpha, P), el0)
    }
    next_ptr := add(ptr, mul(16, points))
}

function gkr_memrel_compress(address_space, addr_low, addr_high, ts_low, ts_high, val_low, val_high) -> compressed {
    compressed := add(mload(add(MEMORY_CHALLS_PTR(), 192)), address_space)
    compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR()), addr_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 32)), addr_high, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 64)), ts_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 96)), ts_high, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 128)), val_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 160)), val_high, P))
}

// Fold five generic lookup tuple columns into an existing Horner accumulator.
// A single helper that took all c0..c9 made solc materialize all ten columns
// at the call boundary and failed stack allocation. Splitting the fold into
// two five-column calls keeps each call boundary small while still supporting
// arbitrary linrel_to_calldata_inner() output for every column.
function gkr_lookrel_compress_half(acc, c0, c1, c2, c3, c4) -> acc_next {
    acc_next := add(mulmod(acc, mload(LOGUP_CHALLS_PTR()), P), c4)
    acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c3)
    acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c2)
    acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c1)
    acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c0)
}
// One β-Horner step: acc·β + c. Callers chain ten of these (see lookrel_horner)
// instead of one 5-arg compress_half, keeping every call boundary at 2 args so the
// enclosing cache/gate function stays inside the EVM stack limit.
function gkr_lookrel_step(acc, c) -> acc_next {
    acc_next := add(mulmod(acc, mload(LOGUP_CHALLS_PTR()), P), c)
}

// Split memrel into a 3-arg low + 4-arg high, composed by the caller as
// add(low(...), high(...)). A single 7-arg gkr_memrel_compress forced solc to
// materialize all 7 expression-args at the call boundary, running the enclosing
// cache function 1 slot too deep (same failure the lookrel split above avoids).
function gkr_memrel_compress_low(address_space, addr_low, addr_high) -> compressed {
    compressed := add(mload(add(MEMORY_CHALLS_PTR(), 192)), address_space)
    compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR()), addr_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 32)), addr_high, P))
}
function gkr_memrel_compress_high(ts_low, ts_high, val_low, val_high) -> compressed {
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 64)), ts_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 96)), ts_high, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 128)), val_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 160)), val_high, P))
}
// Reads one inits/teardowns `top_bits` u32 from the transcript preimage (little-endian,
// at absolute calldata `byteoff`). These are the RAM-set base chunk indices absorbed into
// Fiat-Shamir, so a mismatching value breaks the transcript — safe to read from calldata.
function gkr_inits_teardowns_topbits(byteoff) -> v {
    let w := calldataload(byteoff)
    v := add(add(byte(0, w), shl(8, byte(1, w))), add(shl(16, byte(2, w)), shl(24, byte(3, w))))
}

function gkr_virtual_poly_compose_vars(len, skip) -> eval {
    // let total := add(skip, len)
    let max := sub(GKR_CIRCUIT_LAYER_ROUNDS, skip) // exclusive
    let min := sub(max, len)
    // NO NEED FOR THIS CHECK, WE DO IT VIA RUST
    // if gt(total, GKR_CIRCUIT_LAYER_ROUNDS) { // abort when bad
    //     min := max
    // }
    for { let i := min } lt(i, max) { i := add(i, 1) } {
        eval := add(mul(eval, 2), mload(add(POINT_PTR(), mul(i, 32))))
    }
}
function gkr_virtual_poly_zero_vars(len) -> eval {
    eval := 1
    for { let i := 0 } lt(i, len) { i := add(i, 1) } {
        eval := mulmod(eval, add(1, sub(mul(2, P), mload(add(POINT_PTR(), mul(i, 32))))), P)
    }
}
function gkr_virtual_poly_rangecheck(width) -> eval {
    eval := mulmod(gkr_virtual_poly_compose_vars(width, 0), gkr_virtual_poly_zero_vars(sub(GKR_CIRCUIT_LAYER_ROUNDS, width)), P)
}

function gate_calldataload(idx) -> load {
    load := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, idx))))
}
function gate_mload(idx) -> load {
    load := mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, idx)))
}
function pointcheck_update(acc, alpha, gate) -> next_acc {
    next_acc := add(mulmod(acc, alpha, P), gate)
}
function logup_pointcheck_update(acc, alpha, num_out, den_out) -> next_acc {
    acc := pointcheck_update(acc, alpha, den_out)
    next_acc := pointcheck_update(acc, alpha, num_out)
}
function u128_neg(input) -> neg_input {
    neg_input := sub(mul(2, P), input)
}

// 3
function gate_aggregatelookuprationalpair(alpha, acc, num1_idx, num2_idx, den1_idx, den2_idx) -> next_acc {
    let num1 := gate_calldataload(num1_idx)
    let num2 := gate_calldataload(num2_idx)
    let den1 := gate_calldataload(den1_idx)
    let den2 := gate_calldataload(den2_idx)
    let den_out := mulmod(den1, den2, P)
    let num_out := add(mulmod(num1, den2, P), mulmod(num2, den1, P))
    next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
}
function gate_copyinextensionfield(alpha, acc, input_idx) -> next_acc {
    let input := gate_calldataload(input_idx)
    next_acc := pointcheck_update(acc, alpha, input)
}

// 2
function gate_maskintoidentityproduct(alpha, acc, input_idx, mask_idx) -> next_acc {
    let input := gate_calldataload(input_idx)
    let mask := gate_calldataload(mask_idx)
    // let neg_mask := u128_neg(mask)
    // let gate := add(mulmod(input, mask, P), add(1, neg_mask))
    let neg_one := sub(P, 1)
    let gate := add(mulmod(mask, add(input, neg_one), P), 1)
    next_acc := pointcheck_update(acc, alpha, gate)
}

        function gkr_circuit(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
            ptr, claim,
            alpha := sumcheck_circuit_layer3(ptr, claim, alpha)
            ptr, claim,
            alpha := sumcheck_circuit_layer2(ptr, claim, alpha)
            ptr, claim,
            alpha := sumcheck_circuit_layer1(ptr, claim, alpha)
            ptr, claim,
            alpha := sumcheck_circuit_layer0(ptr, claim, alpha)
            next_ptr := ptr
            next_claim := claim
            next_alpha := alpha
        }

        // Assemble the committed-state preimage and mark_gkr_verified(bytes32) on the
        // registry (own frame — keeps the fallback stack under the EVM limit). Layout
        // mirrors whir.sol: [seed:32][batching:16][opening:16][z:WHIR_Z_COORDS*16]
        // [witCap:CAP*32][setupCap:CAP*32]. NOTE: the packed claims-merge + WHIR batching
        // (validated in the Rust mirror) must run first to populate the batching/opening/z
        // regions (GKR_CIRCUIT_ALPHA2_PTR / claim / POINT_PTR).
        // Assert the remaining proof stream is fully consumed (all-zero tail). In its own
        // frame so the loop counter doesn't add to the tight fallback root stack, which
        // otherwise runs exactly 1 slot too deep on `ptr` (see HEURISTICS.md).
        function assert_proof_empty(ptr) {
            // The GKR stream ends exactly 8 bytes before the end of calldata: the trailing 8
            // bytes are the WHIR-batching PoW nonce (consumed in emit_gkr_mark via
            // calldataload(calldatasize()-8)). Require the cursor to land there precisely.
            if iszero(eq(ptr, sub(calldatasize(), 8))) { revert(0, 0) }
        }

        // Copy `count` little-endian u32s from calldata[cdpos] to memory[wpos] as big-endian.
        // The GKR preimage stores the merkle caps as LE u32; the committed state (and whir.sol)
        // want BE u32 digests, so each 4-byte word is byte-reversed.
        function write_cap_be(wpos, cdpos, count) {
            for { let j := 0 } lt(j, count) { j := add(j, 1) } {
                let le := shr(224, calldataload(add(cdpos, mul(4, j))))
                let be := or(or(shl(24, and(le, 0xff)), shl(16, and(shr(8, le), 0xff))),
                             or(shl(8, and(shr(16, le), 0xff)), shr(24, le)))
                mstore(add(wpos, mul(4, j)), shl(224, be))
            }
        }
        // Interpolate-halve n elements at sc: sc[j] = sc[2j] + (sc[2j+1]-sc[2j])·r.
        function whir_foldhalf(sc, n, r) {
            // canonical interpolation a + (b-a)*r. Reduce a,b mod P first: after several folds
            // the running values accumulate non-canonically (up to ~4P), which would make the
            // old `sub(2*P, a)` underflow once a > 2P (a real bug hit by the last partial chunk).
            let Pm := mload(P_PTR)
            for { let j := 0 } lt(j, div(n, 2)) { j := add(j, 1) } {
                let a := mod(mload(add(sc, mul(64, j))), Pm)
                let b := mod(mload(add(sc, add(mul(64, j), 32))), Pm)
                mstore(add(sc, mul(32, j)), addmod(a, mulmod(addmod(b, sub(Pm, a), Pm), r, Pm), Pm))
            }
        }
        // Fold one 2^4=16-chunk (count real evals from calldata, rest zero) by the 4 packing
        // coords in reversed order (e3,e2,e1,e0) — a 4-var multilinear eval → single claim.
        function whir_fold16(cdbase, count, e0, e1, e2, e3) -> v {
            let sc := add(GKR_ABS_PTR(), 384)
            for { let i := 0 } lt(i, 16) { i := add(i, 1) } {
                let val := 0
                if lt(i, count) {
                val := shr(128, calldataload(add(cdbase, mul(16, i)))) }
                mstore(add(sc, mul(32, i)), val)
            }
            whir_foldhalf(sc, 16, e3)
            whir_foldhalf(sc, 8, e2)
            whir_foldhalf(sc, 4, e1)
            whir_foldhalf(sc, 2, e0)
            v := mload(sc)
        }

        // GKR→WHIR handoff: draw the 4 packing coords, merge the base-layer claims (mem++wit
        // 106→7, setup 10→1), draw the WHIR batching challenge (PoW nonce=0), form the batched
        // opening, and mark_gkr_verified(keccak(preimage)) with preimage
        //   [seed:32][batching:16][opening:16][z = extra(4) ++ base_z(22) : 26·16][caps:2·CAP·32].
        function emit_gkr_mark(claim_v) {
            let sp := SEED_PTR()
            let ex := GKR_ABS_PTR()            // 4 packing coords
            let mg := add(GKR_ABS_PTR(), 128)  // 8 merged claims (7 mem_wit ++ 1 setup)
            // draw 4 packing coords
            let seed := mload(sp)
            for { let i := 0 } lt(i, WHIR_PACK_LOG2) { i := add(i, 1) } {
                seed := keccak256(sp, 32)
                mstore(sp, seed)
                mstore(add(ex, mul(32, i)), mod(shr(128, seed), mload(P_PTR)))
            }
            let e0 := mload(ex)
            let e1 := mload(add(ex, 32))
            let e2 := mload(add(ex, 64))
            let e3 := mload(add(ex, 96))
            // merge base-layer claims (dense in layer0's eval block at CIRCUIT_PTR)
            let cdbase := mload(CIRCUIT_PTR)
            for { let c := 0 } lt(c, WHIR_MERGED_MW) { c := add(c, 1) } {
                let off := mul(c, 16)
                let count := 16
                if gt(add(off, 16), WHIR_NUM_MEMWIT) {
                count := sub(WHIR_NUM_MEMWIT, off) }
                mstore(add(mg, mul(32, c)), whir_fold16(add(cdbase, mul(16, off)), count, e0, e1, e2, e3))
            }
            mstore(add(mg, mul(32, WHIR_MERGED_MW)), whir_fold16(add(cdbase, mul(16, WHIR_NUM_MEMWIT)), WHIR_NUM_SETUP, e0, e1, e2, e3))
            // draw WHIR batching (PoW fold: digest=keccak(seed||nonce_be8), top WHIR_BATCH_POW_BITS
            // must be zero; nonce is the 8-byte BE tail of the calldata). Then draw.
            let wnonce := shr(192, calldataload(sub(calldatasize(), 8)))
            mstore(sp, seed)
            mstore(add(sp, 32), shl(192, wnonce))
            seed := keccak256(sp, 40)
            if shr(sub(256, WHIR_BATCH_POW_BITS), seed) {
            revert(0, 0) }
            mstore(sp, seed)
            seed := keccak256(sp, 32)
            mstore(sp, seed)
            let batching := mod(shr(128, seed), mload(P_PTR))
            // batched opening = Σ merged_i · batching^i
            let opening := 0
            let bexp := 1
            for { let i := 0 } lt(i, add(WHIR_MERGED_MW, 1)) { i := add(i, 1) } {
                opening := addmod(opening, mulmod(mload(add(mg, mul(32, i))), bexp, mload(P_PTR)), mload(P_PTR))
                bexp := mulmod(bexp, batching, mload(P_PTR))
            }
            // preimage
            let base := GKR_INIT_SCRATCH_PTR()
            mstore(base, seed)
            mstore(add(base, 32), shl(128, and(batching, MASK)))
            mstore(add(base, 48), shl(128, and(opening, MASK)))
            let plen := 64
            for { let i := 0 } lt(i, WHIR_PACK_LOG2) { i := add(i, 1) } {
                mstore(add(base, plen), shl(128, and(mload(add(ex, mul(32, i))), MASK)))
                plen := add(plen, 16)
            }
            for { let i := 0 } lt(i, WHIR_BASE_Z_COORDS) { i := add(i, 1) } {
                mstore(add(base, plen), shl(128, and(mload(add(POINT_PTR(), mul(i, 32))), MASK)))
                plen := add(plen, 16)
            }
            // caps: committed state wants [memory_cap][setup_cap] as BE u32. The GKR preimage
            // (in calldata) holds them as LE u32 after registers(384) + final_pc(12) +
            // top_bits(num_teardown_sets*4 = 8): setup_cap @ byte 404, memory_cap @ byte 660.
            // Re-encode to BE and reorder (memory first). count = WHIR_CAP*8 u32s per cap.
            write_cap_be(add(base, plen), 660, mul(WHIR_CAP, 8))                                 // memory
            write_cap_be(add(add(base, plen), mul(mul(WHIR_CAP, 8), 4)), 404, mul(WHIR_CAP, 8))  // setup
            plen := add(plen, mul(mul(2, WHIR_CAP), 32))
            let commitment := keccak256(base, plen)
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
            pop(call(gas(), REGISTRY, 0, 0, 100, 0, 0))
        }

        // SPILL OVERWRITE PREVENTION
        if gt(mload(0x40), MINIMUM_FREE_HEAP_PTR) {
            revert(0, 0)
        }

        // INIT + MAIN. `alpha`, `init_gas`, `compress_gas` are confined to this block so
        // their stack slots free before the tail (assert/emit/return) — the legacy backend
        // does not spill, and keeping them live to the end runs the root `ptr` 1 slot too deep.
        // Gas deltas are stashed to heap (read back in the anti-DCE return), so scoping is safe.
        let ptr, claim
        {
            let alpha
            mstore(GKR_INIT_GAS_PTR(), gas())
            mstore(SEED_PTR(), 0) // SEED Transcript, FINE as long as we don't draw without absorb!
            ptr := transcript_init(0)
            ptr, claim,
            alpha := gkr_init(ptr)
            mstore(GKR_INIT_GAS_PTR(), sub(mload(GKR_INIT_GAS_PTR()), gas()))

            mstore(GKR_MAIN_GAS_PTR(), gas())
            ptr, claim,
            alpha := gkr_compress(ptr, claim, alpha)
            ptr, claim,
            alpha := gkr_circuit(ptr, claim, alpha)
            mstore(GKR_MAIN_GAS_PTR(), sub(mload(GKR_MAIN_GAS_PTR()), gas()))
        }

        // Permutation identity: read-set product == write-set product (no inversions).
        check_permutation_identity()

        // DONE: Proof empty now (own frame — see assert_proof_empty)
        assert_proof_empty(ptr)

        // TODO: don't forget the recursion chain check
        // TODO: very, VERY, carefully review end-to-end fiat-shamir

        // ── GKR→WHIR handoff commitment ────────────────────────────────────────
        // Assemble the committed-state preimage the WHIR verifier will hash, keccak it,
        // and mark_gkr_verified(bytes32). In its own function frame to keep the tight
        // fallback stack under the EVM limit (see HEURISTICS.md).
        emit_gkr_mark(claim)

        // anti-DCE
        mstore(0, claim)
        mstore(32, mload(GKR_INIT_GAS_PTR()))
        mstore(64, mload(GKR_MAIN_GAS_PTR()))
        mstore(96, ptr)
        return(0, 128)
    } }
}
