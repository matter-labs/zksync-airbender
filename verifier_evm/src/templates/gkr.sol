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
    uint256 constant __TEMPLATE_MERKLE_TREE_CAPS_BYTES = 512; // 16 caps * 32-byte hash
    // Proth120 packed-mode: keccak preimage = commit_initial_u32 bytes
    // (inits_and_teardowns_top_bits as LE u32 || setup cap digests || merged mem cap digests).
    // 520 for this proof (unified_reduced_machine, 2^22, pack_log2=4). See gkr_transcript_reference.md.
    uint256 constant __TEMPLATE_GKR_INIT_PREIMAGE_BYTES = 916; // registers(384) + final_pc(12) + top_bits(8) + setup_cap(256) + memory_cap(256)
    uint256 constant __TEMPLATE_EXTERNAL_POW_BITS       = 20;  // external-challenge PoW difficulty (max(lookup, 20))
    uint256 constant __TEMPLATE_EXPECTED_FINAL_PC       = 384; // program's terminal PC — binds the verified statement to this program

    // ── GKR init (fold the 8 init polys into the first sumcheck claim) ────────
    uint256 constant GKR_INIT_BYTES          = 2560; // 10 output polys * 16 elems * 16 bytes (Proth120)
    uint256 constant GKR_INIT_POLY_BYTES     = 256;  // 16 elems * 16 bytes (literal; Yul rejects const exprs)

    // ── GKR compression ───────────────────────────────────────────────────────
    uint256 constant GKR_COMPRESSION_POINTCHECK_POLY_BYTES = 64;  // 4 * 16
    uint256 constant GKR_COMPRESSION_POINTCHECK_BYTES      = 512; // 8 * 64

    // ── GKR circuit ───────────────────────────────────────────────────────────
    uint256 constant __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS = 22;

    // ── Committed-state handoff to WHIR (via the shared registry) ──────────────
    // After GKR verifies, it assembles the SAME committed-state preimage the WHIR
    // verifier hashes — [seed:32][batching:16][opening:16][z_initial:nz*16]
    // [witness_cap:CAP*32][setup_cap:CAP*32] — keccaks it, and marks it. WHIR
    // recomputes the same bytes32 in its own tx; the registry events must match.
    uint256 constant REGISTRY          = 0xCAFE0001;
    uint256 constant MARK_GKR_SELECTOR = 0xef4f148a; // mark_gkr_verified(bytes32,bytes32,bytes32)
    uint256 constant __TEMPLATE_WHIR_Z_COORDS     = 26;         // 22 base + 4 packing extra coords
    uint256 constant __TEMPLATE_WHIR_CAP          = 8;          // CAP (witness+setup base-oracle caps)
    uint256 constant __TEMPLATE_WHIR_BATCH_POW_BITS = 11;       // batched_proximity_check_pow_bits (Sec100)
    // GKR->WHIR handoff (MergedAndPackedMemoryAndWitness, pack_log2=4). Base-layer at-point
    // claims (dense in layer0's calldata eval block): mem++wit = 104 cols, setup = 10 cols.
    // Merge folds each 2^pack_log2=16-chunk by the 4 packing coords: 104->7, 10->1.
    uint256 constant __TEMPLATE_WHIR_PACK_LOG2    = 4;
    uint256 constant __TEMPLATE_WHIR_NUM_MEMWIT   = 104;        // memory_layout + witness_layout total widths
    uint256 constant __TEMPLATE_WHIR_NUM_SETUP    = 10;         // generic_lookup_tables_width
    uint256 constant __TEMPLATE_WHIR_MERGED_MW    = 7;          // ceil(104/16)
    uint256 constant __TEMPLATE_WHIR_BASE_Z_COORDS = 22;        // layer-0 folding point length

    fallback() external {
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
            ptr := add(POINT_PTR(), mul(32, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS))
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

        // Layer-0 table-driven quadratic-gate evaluation (size opt). GATEVAL holds one reduced
        // value per quadratic gate (filled by the compact bucket loops from GKR_QTABLE, read by
        // the Horner chunk functions as `mload(GATEVAL+32*slot)`). QTABLE is the packed record
        // stream (slot,a,b,coeff) written via mstore immediates. Both live in the pristine (zero,
        // never-written) heap window above the widest claims array (< slot 288), so GATEVAL needs
        // no zeroing. Only used during layer 0's point-check; nothing else touches these slots.
        function GKR_GATEVAL_PTR() -> ptr {
        ptr := add(SEED_PTR(), mul(32, 288)) }
        function GKR_QTABLE_PTR() -> ptr {
        ptr := add(SEED_PTR(), mul(32, 420)) }

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

        function transcript_4to1_dual(w0, w1, modulus) -> r {
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
            r := mod(shr(128, seed), modulus)
        }

        // alpha is the batching challenge needed right after checking outputs



        // alpha is the batching challenge needed right folding point claims

        function transcript_init(ptr) -> next_ptr {
            // Proth120 packed-mode transcript (MergedAndPackedMemoryAndWitness), validated
            // keccak-for-keccak in step1_test/GkrStep1.sol against the real proof.
            //   seed = keccak256(preimage)                       // commit_initial_u32 (916 B: regs+PC+topbits+caps)
            //   nonce = calldata[preimage..preimage+8] (BE u64)
            //   seed = keccak256(seed || be8(nonce)); require top __TEMPLATE_EXTERNAL_POW_BITS bits zero
            //   for i in 0..9: seed = keccak256(seed); ch = (seed>>128) % P
            //   ch[0..7] -> MEMORY_CHALLS (6 perm-linearization + additive), ch[7..9] -> LOGUP (alpha, additive)
            calldatacopy(SEED_PTR(), ptr, __TEMPLATE_GKR_INIT_PREIMAGE_BYTES)
            let seed := keccak256(SEED_PTR(), __TEMPLATE_GKR_INIT_PREIMAGE_BYTES)

            // PoW fold: digest = keccak(seed(32) || nonce_be8); require top __TEMPLATE_EXTERNAL_POW_BITS zero.
            let nonce := shr(192, calldataload(add(ptr, __TEMPLATE_GKR_INIT_PREIMAGE_BYTES))) // 8-byte BE nonce
            mstore(SEED_PTR(), seed)
            mstore(add(SEED_PTR(), 32), 0)
            seed := keccak256(SEED_PTR(), 40)
            if shr(sub(256, __TEMPLATE_EXTERNAL_POW_BITS), seed) { revert(0, 0) } // PoW: top pow_bits must be zero

            // draw 9 challenges (each: seed=keccak(seed); take top 128 bits mod P)
            mstore(SEED_PTR(), seed)
            seed := keccak256(SEED_PTR(), 32) mstore(SEED_PTR(), seed) mstore(MEMORY_CHALLS_PTR(),               mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32) mstore(SEED_PTR(), seed) mstore(add(MEMORY_CHALLS_PTR(), 32),       mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32) mstore(SEED_PTR(), seed) mstore(add(MEMORY_CHALLS_PTR(), 64),       mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32) mstore(SEED_PTR(), seed) mstore(add(MEMORY_CHALLS_PTR(), 96),       mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32) mstore(SEED_PTR(), seed) mstore(add(MEMORY_CHALLS_PTR(), 128),      mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32) mstore(SEED_PTR(), seed) mstore(add(MEMORY_CHALLS_PTR(), 160),      mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32) mstore(SEED_PTR(), seed) mstore(add(MEMORY_CHALLS_PTR(), 192),      mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32) mstore(SEED_PTR(), seed) mstore(LOGUP_CHALLS_PTR(),                 mod(shr(128, seed), mload(P_PTR)))
            seed := keccak256(SEED_PTR(), 32) mstore(SEED_PTR(), seed) mstore(add(LOGUP_CHALLS_PTR(), 32),        mod(shr(128, seed), mload(P_PTR)))

            // SEED_PTR now holds the post-STEP-1 seed; the GKR entry (gkr_init) absorbs output evals next.
            next_ptr := add(ptr, add(__TEMPLATE_GKR_INIT_PREIMAGE_BYTES, 8)) // preimage + 8-byte PoW nonce
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
                seed := keccak256(sp, 32) mstore(sp, seed)
                mstore(add(POINT_PTR(), mul(i, 32)), mod(shr(128, seed), mload(P_PTR)))
            }
            seed := keccak256(sp, 32) mstore(sp, seed)
            mstore(GKR_BATCHING_PTR(), mod(shr(128, seed), mload(P_PTR)))

            // eq[16] over eval_point[4] (MSB-first: eq[j] = Π_v (bit_{3-v}(j)? z[v] : 1-z[v]))
            for { let j := 0 } lt(j, 16) { j := add(j, 1) } {
                let e := 1
                for { let v := 0 } lt(v, 4) { v := add(v, 1) } {
                    let zv := mload(add(POINT_PTR(), mul(v, 32)))
                    let bit := and(shr(sub(3, v), j), 1)
                    // f = bit ? zv : (1 - zv)   (non-canonical 1-zv = 1 + (P - zv))
                    let f := zv
                    if iszero(bit) { f := add(1, sub(mload(P_PTR), zv)) }
                    e := mulmod(e, f, mload(P_PTR))
                }
                mstore(add(GKR_EQ_PTR(), mul(j, 32)), e)
            }
            // 10 claims: claim_c = Σ_j outputEval[c*16+j] * eq[j]  (column c, 16 evals)
            for { let c := 0 } lt(c, 10) { c := add(c, 1) } {
                let acc := 0
                for { let j := 0 } lt(j, 16) { j := add(j, 1) } {
                    let k := add(mul(c, 16), j)
                    let val := shr(128, calldataload(add(ptr, mul(k, 16))))
                    acc := add(mulmod(val, mload(add(GKR_EQ_PTR(), mul(j, 32))), mload(P_PTR)), acc)
                }
                mstore(add(GKR_CLAIMS_PTR(), mul(c, 32)), mod(acc, mload(P_PTR)))
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
                if iszero(eq(pcv, __TEMPLATE_EXPECTED_FINAL_PC)) {
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
            let modulus := mload(P_PTR)
            eq_scale := 1
            for { let i := 0 } lt(i, total_rounds) { i := add(i, 1) } {
                let w0 := calldataload(ptr)
                let w1 := calldataload(add(ptr, 32))
                let c0 := shr(128, w0)
                let c1 := and(w0, MASK)
                let c2 := shr(128, w1)
                let c3 := and(w1, MASK)
                let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, modulus)
                let r := transcript_4to1_dual(w0, w1, modulus) // before-check draw is intentional; see HEURISTICS.md
                // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
                if mod(add(claim, sub(modulus, g0g1_scaled)), modulus) {
                revert(0, 0) }
                claim := add(mulmod(add(mulmod(add(mulmod(c3, r, modulus), c2), r, modulus), c1), r, modulus), c0)
                let z := mload(add(POINT_PTR(), mul(i, 32)))
                let zr := mulmod(z, r, modulus)
                eq_scale := add(add(add(zr, zr), 1), sub(mul(4, modulus), add(z, r)))
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
            let modulus := mload(P_PTR)
            let SI := GKR_EQ_PTR() // reuse eq scratch as the sorted-index array (10 slots)
            for { let li := 0 } lt(li, 10) { li := add(li, 1) } { mstore(add(SI, mul(li, 32)), li) }
            if boundary {
                mstore(add(SI, 0), 6) mstore(add(SI, 32), 7)
                mstore(add(SI, 64), 0) mstore(add(SI, 96), 1) mstore(add(SI, 128), 2)
                mstore(add(SI, 160), 3) mstore(add(SI, 192), 4) mstore(add(SI, 224), 5)
                mstore(add(SI, 256), 8) mstore(add(SI, 288), 9)
            }
            let g := 0
            let gb := 1
            for { let step := 0 } lt(step, 2) { step := add(step, 1) } {
                let word := calldataload(add(cp, mul(mload(add(SI, mul(step, 32))), 32)))
                g := add(mulmod(gb, mulmod(shr(128, word), and(word, MASK), modulus), modulus), g)
                gb := mulmod(gb, batching, modulus)
            }
            for { let pr := 0 } lt(pr, 3) { pr := add(pr, 1) } {
                let wN := calldataload(add(cp, mul(mload(add(SI, mul(add(2, mul(pr, 2)), 32))), 32)))
                let wD := calldataload(add(cp, mul(mload(add(SI, mul(add(3, mul(pr, 2)), 32))), 32)))
                let num := add(mulmod(shr(128, wN), and(wD, MASK), modulus), mulmod(and(wN, MASK), shr(128, wD), modulus))
                let den := mulmod(shr(128, wD), and(wD, MASK), modulus)
                g := add(mulmod(gb, num, modulus), g)
                gb := mulmod(gb, batching, modulus)
                g := add(mulmod(gb, den, modulus), g)
                gb := mulmod(gb, batching, modulus)
            }
            for { let step := 8 } lt(step, 10) { step := add(step, 1) } {
                let word := calldataload(add(cp, mul(mload(add(SI, mul(step, 32))), 32)))
                g := add(mulmod(gb, mulmod(shr(128, word), and(word, MASK), modulus), modulus), g)
                gb := mulmod(gb, batching, modulus)
            }
            if mod(add(mulmod(mod(g, modulus), eq_scale, modulus), sub(modulus, claim)), modulus) {
            revert(0, 0) }
            // absorb the 320 B of LSB lines (sorted transcript order), draw r_last + next_batching
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            calldatacopy(add(GKR_ABS_PTR(), 32), cp, 320)
            let seed := keccak256(GKR_ABS_PTR(), 352)
            mstore(SEED_PTR(), seed)
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            let r_last := mod(shr(128, seed), modulus)
            seed := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), seed)
            nbatch := mod(shr(128, seed), modulus)
            mstore(add(POINT_PTR(), mul(fs, 32)), r_last)
            // next claims = interpolate lsb_sorted at r_last (no perm): a + (b-a)*r_last
            for { let li := 0 } lt(li, 10) { li := add(li, 1) } {
                let word := calldataload(add(cp, mul(li, 32)))
                let a := shr(128, word)
                mstore(add(GKR_CLAIMS_PTR(), mul(li, 32)), add(a, mulmod(add(and(word, MASK), sub(modulus, a)), r_last, modulus)))
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
                ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, fs)
                ptr, batching := gkr_dr_final(ptr, fs, batching, eq(k, 17), eq_scale, claim)
            }
            mstore(GKR_BATCHING_PTR(), batching)
            next_ptr := ptr
            next_claim := 0
            next_alpha := batching
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

        // Assemble the committed-state preimage and mark_gkr_verified(bytes32) on the
        // registry (own frame — keeps the fallback stack under the EVM limit). Layout
        // mirrors whir.sol: [seed:32][batching:16][opening:16][z:__TEMPLATE_WHIR_Z_COORDS*16]
        // [witCap:CAP*32][setupCap:CAP*32]. NOTE: the packed claims-merge + WHIR batching
        // (validated in the Rust mirror) must run first to populate the batching/opening/z
        // regions (GKR_CIRCUIT_ALPHA2_PTR / claim / POINT_PTR).
        // Assert the remaining proof stream is fully consumed (all-zero tail). In its own
        // frame so the loop counter doesn't add to the tight fallback root stack, which
        // otherwise runs exactly 1 slot too deep on `ptr` (see HEURISTICS.md).
        function assert_proof_empty(ptr) {
            for { let i := 0 } lt(i, 10) { i := add(i, 1) } {
                if calldataload(add(ptr, mul(i, 32))) { revert(0, 0) }
            }
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
            for { let j := 0 } lt(j, div(n, 2)) { j := add(j, 1) } {
                let a := mload(add(sc, mul(64, j)))
                let b := mload(add(sc, add(mul(64, j), 32)))
                mstore(add(sc, mul(32, j)), add(a, mulmod(add(b, sub(mul(2, mload(P_PTR)), a)), r, mload(P_PTR))))
            }
        }
        // Fold one 2^4=16-chunk (count real evals from calldata, rest zero) by the 4 packing
        // coords in reversed order (e3,e2,e1,e0) — a 4-var multilinear eval → single claim.
        function whir_fold16(cdbase, count, e0, e1, e2, e3) -> v {
            let sc := add(GKR_ABS_PTR(), 384)
            for { let i := 0 } lt(i, 16) { i := add(i, 1) } {
                let val := 0
                if lt(i, count) { val := shr(128, calldataload(add(cdbase, mul(16, i)))) }
                mstore(add(sc, mul(32, i)), val)
            }
            whir_foldhalf(sc, 16, e3)
            whir_foldhalf(sc, 8, e2)
            whir_foldhalf(sc, 4, e1)
            whir_foldhalf(sc, 2, e0)
            v := mload(sc)
        }

        // GKR→WHIR handoff: draw the 4 packing coords, merge the base-layer claims (mem++wit
        // 104→7, setup 10→1), draw the WHIR batching challenge (PoW nonce=0), form the batched
        // opening, and mark_gkr_verified(keccak(preimage)) with preimage
        //   [seed:32][batching:16][opening:16][z = extra(4) ++ base_z(22) : 26·16][caps:2·CAP·32].
        function emit_gkr_mark(claim_v) {
            let sp := SEED_PTR()
            let ex := GKR_ABS_PTR()            // 4 packing coords
            let mg := add(GKR_ABS_PTR(), 128)  // 8 merged claims (7 mem_wit ++ 1 setup)
            // draw 4 packing coords
            let seed := mload(sp)
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_PACK_LOG2) { i := add(i, 1) } {
                seed := keccak256(sp, 32)
                mstore(sp, seed)
                mstore(add(ex, mul(32, i)), mod(shr(128, seed), mload(P_PTR)))
            }
            let e0 := mload(ex) let e1 := mload(add(ex, 32)) let e2 := mload(add(ex, 64)) let e3 := mload(add(ex, 96))
            // merge base-layer claims (dense in layer0's eval block at CIRCUIT_PTR)
            let cdbase := mload(CIRCUIT_PTR)
            for { let c := 0 } lt(c, __TEMPLATE_WHIR_MERGED_MW) { c := add(c, 1) } {
                let off := mul(c, 16)
                let count := 16
                if gt(add(off, 16), __TEMPLATE_WHIR_NUM_MEMWIT) {
                count := sub(__TEMPLATE_WHIR_NUM_MEMWIT, off) }
                mstore(add(mg, mul(32, c)), whir_fold16(add(cdbase, mul(16, off)), count, e0, e1, e2, e3))
            }
            mstore(add(mg, mul(32, __TEMPLATE_WHIR_MERGED_MW)), whir_fold16(add(cdbase, mul(16, __TEMPLATE_WHIR_NUM_MEMWIT)), __TEMPLATE_WHIR_NUM_SETUP, e0, e1, e2, e3))
            // draw WHIR batching (PoW fold: digest=keccak(seed||nonce_be8), top __TEMPLATE_WHIR_BATCH_POW_BITS
            // must be zero; nonce is the 8-byte BE tail of the calldata). Then draw.
            let wnonce := shr(192, calldataload(sub(calldatasize(), 8)))
            mstore(sp, seed)
            mstore(add(sp, 32), shl(192, wnonce))
            seed := keccak256(sp, 40)
            if shr(sub(256, __TEMPLATE_WHIR_BATCH_POW_BITS), seed) {
            revert(0, 0) }
            mstore(sp, seed)
            seed := keccak256(sp, 32)
            mstore(sp, seed)
            let batching := mod(shr(128, seed), mload(P_PTR))
            // batched opening = Σ merged_i · batching^i
            let opening := 0
            let bexp := 1
            for { let i := 0 } lt(i, add(__TEMPLATE_WHIR_MERGED_MW, 1)) { i := add(i, 1) } {
                opening := addmod(opening, mulmod(mload(add(mg, mul(32, i))), bexp, mload(P_PTR)), mload(P_PTR))
                bexp := mulmod(bexp, batching, mload(P_PTR))
            }
            // preimage
            let base := GKR_INIT_SCRATCH_PTR()
            mstore(base, seed)
            mstore(add(base, 32), shl(128, and(batching, MASK)))
            mstore(add(base, 48), shl(128, and(opening, MASK)))
            let plen := 64
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_PACK_LOG2) { i := add(i, 1) } {
                mstore(add(base, plen), shl(128, and(mload(add(ex, mul(32, i))), MASK)))
                plen := add(plen, 16)
            }
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_BASE_Z_COORDS) { i := add(i, 1) } {
                mstore(add(base, plen), shl(128, and(mload(add(POINT_PTR(), mul(i, 32))), MASK)))
                plen := add(plen, 16)
            }
            // caps: committed state wants [memory_cap][setup_cap] as BE u32. The GKR preimage
            // (in calldata) holds them as LE u32 after registers(384) + final_pc(12) +
            // top_bits(num_teardown_sets*4 = 8): setup_cap @ byte 404, memory_cap @ byte 660.
            // Re-encode to BE and reorder (memory first). count = __TEMPLATE_WHIR_CAP*8 u32s per cap.
            write_cap_be(add(base, plen), 660, mul(__TEMPLATE_WHIR_CAP, 8))                                 // memory
            write_cap_be(add(add(base, plen), mul(mul(__TEMPLATE_WHIR_CAP, 8), 4)), 404, mul(__TEMPLATE_WHIR_CAP, 8))  // setup
            plen := add(plen, mul(mul(2, __TEMPLATE_WHIR_CAP), 32))
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
            mstore(4, keccak256(base, plen))
            pop(call(gas(), REGISTRY, 0, 0, 36, 0, 0))
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
            ptr, claim, alpha := gkr_init(ptr)
            mstore(GKR_INIT_GAS_PTR(), sub(mload(GKR_INIT_GAS_PTR()), gas()))

            mstore(GKR_MAIN_GAS_PTR(), gas())
            ptr, claim, alpha := gkr_compress(ptr, claim, alpha)
            ptr, claim, alpha := gkr_circuit(ptr, claim, alpha)
            mstore(GKR_MAIN_GAS_PTR(), sub(mload(GKR_MAIN_GAS_PTR()), gas()))
        }

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
        uint256 max = 24 - skip; // __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS
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
