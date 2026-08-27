// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.36;

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
    // (→ "stack too deep"). Store P once at a heap offset and `mload(P_PTR)` it instead. The
    // generated circuit.yul and the hand-written ops both use `mload(P_PTR)`; `mstore(P_PTR, P)`
    // runs first in the fallback.
    //
    // MEMORY LAYOUT (matters under via_ir): solc's IR backend places its stack-spill slots at
    // fixed low offsets that grow up from 0x80, and the SPILL-OVERWRITE guard (end of the
    // fallback) asserts they never reach MINIMUM_FREE_HEAP_PTR. So the region
    // [0x80, MINIMUM_FREE_HEAP_PTR) is the spill zone and [MINIMUM_FREE_HEAP_PTR, ∞) is
    // spill-safe. P_PTR / CIRCUIT_PTR MUST live in the safe region — a low fixed slot (the old
    // 160/192) is silently clobbered by via_ir spills, corrupting the committed state. They take
    // the first two slots of the safe region; the hand-placed heap (MEMORY_CHALLS_PTR) starts 64
    // bytes higher. INVARIANT (Yul forbids constant arithmetic in assembly, so these are spelled
    // as literals): P_PTR == MINIMUM_FREE_HEAP_PTR, CIRCUIT_PTR == MINIMUM_FREE_HEAP_PTR + 32,
    // MEMORY_CHALLS_PTR == MINIMUM_FREE_HEAP_PTR + 64. Bump all four together if the spill zone
    // ever needs more room.
    uint256 constant P_PTR  = 7588;      // == MINIMUM_FREE_HEAP_PTR  (spill-safe slot 0)
    // Fixed heap slot holding the circuit-layer calldata cursor, so gate/cache sub-functions
    // read it via mload instead of a `ptr` parameter (that param was the single deepest stack
    // slot pushing each of them 1 over the EVM limit). Spill-safe slot 1, just above P_PTR.
    uint256 constant CIRCUIT_PTR = 7620; // == MINIMUM_FREE_HEAP_PTR + 32
    uint256 constant ROUNDS = 200; // test-harness only (GKRStreamGen); stripped from production

    // ── Transcript init (absorb caps, derive memory/logup challenges) ─────────
    uint256 constant __TEMPLATE_MERKLE_TREE_CAPS_BYTES = 512; // 16 caps * 32-byte hash
    // Proth120 packed-mode: keccak preimage = commit_initial_u32 bytes
    // (inits_and_teardowns_top_bits as LE u32 || setup cap digests || merged mem cap digests).
    // 520 for this proof (unified_reduced_machine, 2^22, pack_log2=4). See gkr_transcript_reference.md.
    uint256 constant __TEMPLATE_GKR_INIT_PREIMAGE_BYTES = 916; // registers(384) + final_pc(12) + top_bits(8) + setup_cap(256) + memory_cap(256)
    uint256 constant __TEMPLATE_EXTERNAL_POW_BITS       = 20;  // external-challenge PoW difficulty (max(lookup, 20))
    uint256 constant __TEMPLATE_EXPECTED_FINAL_PC       = 1717376; // program's terminal PC — binds the verified statement to this program

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
    address constant __TEMPLATE_REGISTRY_ADDRESS          = 0x00000000000000000000000000000000caFe0001;
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
            // +64: the first two safe slots hold P_PTR and CIRCUIT_PTR (see the layout note).
            ptr := add(MINIMUM_FREE_HEAP_PTR, 64)
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
            //
            // canonicalize the 4 packed field lanes (mod P) before absorbing, so the transcript
            // binds to the reduced value, not the prover's 16-byte encoding (each value has
            // ~2^128/P ≈ 36 encodings). Re-pack keeps the [hi|lo] layout.
            mstore(add(SEED_PTR(), 32), or(shl(128, mod(shr(128, w0), modulus)), mod(and(w0, MASK), modulus)))
            mstore(add(SEED_PTR(), 64), or(shl(128, mod(shr(128, w1), modulus)), mod(and(w1, MASK), modulus)))
            let seed := keccak256(SEED_PTR(), 96) // absorb 4 (canonicalized) coeffs
            mstore(SEED_PTR(), seed)
            seed := keccak256(SEED_PTR(), 32)     // draw
            mstore(SEED_PTR(), seed)
            r := mod(shr(128, seed), modulus)
        }

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
            mstore(add(SEED_PTR(), 32), shl(192, nonce))
            seed := keccak256(SEED_PTR(), 40)
            if shr(sub(256, __TEMPLATE_EXTERNAL_POW_BITS), seed) { revert(0, 0) } // PoW: top pow_bits must be zero

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
            // absorb output evals: seed = keccak(seed || outputEvals). The 2560 B are bulk-copied
            // raw; canonicity is enforced at the use site below — the claims loop reads every one
            // of these 160 lanes and range-checks `val < P`, so any accepted proof has canonical
            // evals and hence a canonical absorb (cheaper than reduce-on-copy: it reuses the read
            // the claims loop already performs).
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

            // eq[16] over eval_point[4] (LSB binding: eq[j] = Π_v (bit_v(j)? z[v] : 1-z[v]),
            // index bit v pairs with point coordinate v — matches the prover's
            // make_eq_table_lsb_first over the drawn point)
            for { let j := 0 } lt(j, 16) { j := add(j, 1) } {
                let e := 1
                for { let v := 0 } lt(v, 4) { v := add(v, 1) } {
                    let zv := mload(add(POINT_PTR(), mul(v, 32)))
                    let bit := and(shr(v, j), 1)
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
                    // reject a non-canonical lane so the bulk-absorbed output evals bind to
                    // reduced values (see the absorb note above)
                    if iszero(lt(val, mload(P_PTR))) { revert(0, 0) }
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

        // Lookup identities — the logup analogue of the permutation-identity check, mirroring the
        // CPU verifier's `gkr_lookup_identity_failed` gate. The 10 GKR output columns are laid out
        // in OutputType order [Perm(0,1), Lookup16Bits(2,3), LookupTimestamps(4,5),
        // GenericLookup(6,7), InitsAndTeardowns(8,9)] as 16 boundary evals each (u128 hi-lane at
        // `op + (col*16 + j)*16`). Each lookup argument is a (numerator, denominator) pair; its
        // rational sum Σ_j num_j/den_j over the 16 evals must be exactly zero. Accumulate the sum
        // as a single fraction — acc_num = acc_num·d + n·acc_den, acc_den = acc_den·d — and require
        // acc_num == 0 with acc_den ≠ 0 (a vanishing denominator would make the sum ill-defined).
        // `op` is the output-evals calldata base (the pointer gkr_init read the evals from).
        function check_lookup_identities(op) {
            let modulus := mload(P_PTR)
            // 3 lookup pairs at columns (2,3),(4,5),(6,7) — the fixed unified-circuit output layout
            // (2 permutation + 3 lookup + 2 inits/teardowns polys = the 10 columns above).
            for { let lk := 0 } lt(lk, 3) { lk := add(lk, 1) } {
                let num_base := add(op, mul(mul(add(2, mul(lk, 2)), 16), 16)) // col (2+2·lk), eval 0
                let den_base := add(num_base, mul(16, 16))                    // col (3+2·lk), eval 0
                let acc_num := 0
                let acc_den := 1
                for { let j := 0 } lt(j, 16) { j := add(j, 1) } {
                    let n := shr(128, calldataload(add(num_base, mul(j, 16))))
                    let d := shr(128, calldataload(add(den_base, mul(j, 16))))
                    acc_num := addmod(mulmod(acc_num, d, modulus), mulmod(n, acc_den, modulus), modulus)
                    acc_den := mulmod(acc_den, d, modulus)
                }
                // Σ num/den == 0 with a non-vanishing denominator.
                if acc_num { revert(0, 0) }
                if iszero(acc_den) { revert(0, 0) }
            }
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
            for { let li := 0 } lt(li, 10) { li := add(li, 1) } {
            mstore(add(SI, mul(li, 32)), li) }
            // Reorder the offset-stored LSB lines into logical (OutputType-group) order so
            // grand-products land at slots 0,1,8,9. Generated from the artifact's
            // global_output_map value offsets (iteration order).
            if boundary {
                mstore(add(SI, 0), 2)
                mstore(add(SI, 32), 3)
                mstore(add(SI, 64), 0)
                mstore(add(SI, 96), 1)
                mstore(add(SI, 128), 4)
                mstore(add(SI, 160), 5)
                mstore(add(SI, 192), 6)
                mstore(add(SI, 224), 7)
                mstore(add(SI, 256), 8)
                mstore(add(SI, 288), 9)
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
            // r_last binds bit 0 of the NEXT layer's enumeration, so the new claim point is
            // [r_last, r_0, .., r_{fs-1}] in plain variable order: shift the round challenges
            // up by one slot and prepend (mirrors the CPU generator's LSB fix).
            for { let sh := fs } gt(sh, 0) { sh := sub(sh, 1) } {
                mstore(add(POINT_PTR(), mul(sh, 32)), mload(add(POINT_PTR(), mul(sub(sh, 1), 32))))
            }
            mstore(POINT_PTR(), r_last)
            // next claims = interpolate lsb_sorted at r_last (no perm): a + (b-a)*r_last
            for { let li := 0 } lt(li, 10) { li := add(li, 1) } {
                let word := calldataload(add(cp, mul(li, 32)))
                let a := shr(128, word)
                let b := and(word, MASK)
                // this loop reads all 10 words (= 20 lanes) of the 320 B LSB-lines absorbed
                // above, so requiring both lanes < P makes any accepted proof's absorb canonical
                if iszero(lt(a, modulus)) { revert(0, 0) }
                if iszero(lt(b, modulus)) { revert(0, 0) }
                mstore(add(GKR_CLAIMS_PTR(), mul(li, 32)), add(a, mulmod(add(b, sub(modulus, a)), r_last, modulus)))
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

function sumcheck_circuit_layer4(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl4(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc := 0
            mstore(CIRCUIT_PTR, ptr)
            scl4_caches()
            acc := scl4_g0(alpha, acc)
    let rhs_scaled := mulmod(acc, eq_scale, mload(P_PTR))
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(mload(P_PTR), rhs_scaled)), mload(P_PTR)) { revert(0, 0) }

    
            // WRITEBACK claims for next layer (12 evals) + canonicity guard
                for { let wk := 0 } lt(wk, 12) { wk := add(wk, 1) } {
                    let cv := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk))))
                    if iszero(lt(cv, mload(P_PTR))) { revert(0, 0) }
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), cv)
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // absorb final_step ++ extras in one keccak, THEN draw). next_claim unused (sccl recomputes).
    next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, 12)
}

            function scl4_caches() {
            }
            function scl4_g0(alpha, a) -> acc { acc := a
    // CopyInExtensionField: [11] = 9
    acc := gate_copyinextensionfield(alpha, acc, 11)
    
    // CopyInExtensionField: [10] = 8
    acc := gate_copyinextensionfield(alpha, acc, 10)
    
    // CopyInExtensionField: [7] = 7
    acc := gate_copyinextensionfield(alpha, acc, 7)
    
    // CopyInExtensionField: [6] = 6
    acc := gate_copyinextensionfield(alpha, acc, 6)
    
    // CopyInExtensionField: [5] = 5
    acc := gate_copyinextensionfield(alpha, acc, 5)
    
    // CopyInExtensionField: [4] = 4
    acc := gate_copyinextensionfield(alpha, acc, 4)
    
    // CopyInExtensionField: [9] = 3
    acc := gate_copyinextensionfield(alpha, acc, 9)
    
    // CopyInExtensionField: [8] = 2
    acc := gate_copyinextensionfield(alpha, acc, 8)
    
    // AggregateLookupRationalPair: [2]/[3] + [0]/[1] = 0/1
    acc := gate_aggregatelookuprationalpair(alpha, acc, 2, 0, 3, 1)
    
            }
            function sccl4(alpha) -> claim {
            let src := GKR_CLAIMS_PTR()
            claim := 0
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 0))))
            }
function sumcheck_circuit_layer3(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl3(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc := 0
            mstore(CIRCUIT_PTR, ptr)
            scl3_caches()
            acc := scl3_g0(alpha, acc)
    let rhs_scaled := mulmod(acc, eq_scale, mload(P_PTR))
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(mload(P_PTR), rhs_scaled)), mload(P_PTR)) { revert(0, 0) }

    
            // WRITEBACK claims for next layer (18 evals) + canonicity guard
                for { let wk := 0 } lt(wk, 18) { wk := add(wk, 1) } {
                    let cv := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk))))
                    if iszero(lt(cv, mload(P_PTR))) { revert(0, 0) }
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), cv)
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // absorb final_step ++ extras in one keccak, THEN draw). next_claim unused (sccl recomputes).
    next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, 18)
}

            function scl3_caches() {
            }
            function scl3_g0(alpha, a) -> acc { acc := a
    // CopyInExtensionField: [17] = 11
    acc := gate_copyinextensionfield(alpha, acc, 17)
    
    // CopyInExtensionField: [16] = 10
    acc := gate_copyinextensionfield(alpha, acc, 16)
    
    // CopyInExtensionField: [1] = 9
    acc := gate_copyinextensionfield(alpha, acc, 1)
    
    // CopyInExtensionField: [0] = 8
    acc := gate_copyinextensionfield(alpha, acc, 0)
    
    // AggregateLookupRationalPair: [14]/[15] + [12]/[13] = 6/7
    acc := gate_aggregatelookuprationalpair(alpha, acc, 14, 12, 15, 13)
    
    // AggregateLookupRationalPair: [10]/[11] + [8]/[9] = 4/5
    acc := gate_aggregatelookuprationalpair(alpha, acc, 10, 8, 11, 9)
    
    // CopyInExtensionField: [3] = 3
    acc := gate_copyinextensionfield(alpha, acc, 3)
    
    // CopyInExtensionField: [2] = 2
    acc := gate_copyinextensionfield(alpha, acc, 2)
    
    // AggregateLookupRationalPair: [6]/[7] + [4]/[5] = 0/1
    acc := gate_aggregatelookuprationalpair(alpha, acc, 6, 4, 7, 5)
    
            }
            function sccl3(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := 0
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 11))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 10))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 0))))
            }
function sumcheck_circuit_layer2(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl2(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc := 0
            mstore(CIRCUIT_PTR, ptr)
            scl2_caches()
            acc := scl2_g0(alpha, acc)
            acc := scl2_g1(alpha, acc)
    let rhs_scaled := mulmod(acc, eq_scale, mload(P_PTR))
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(mload(P_PTR), rhs_scaled)), mload(P_PTR)) { revert(0, 0) }

    
            // WRITEBACK claims for next layer (26 evals) + canonicity guard
                for { let wk := 0 } lt(wk, 26) { wk := add(wk, 1) } {
                    let cv := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk))))
                    if iszero(lt(cv, mload(P_PTR))) { revert(0, 0) }
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), cv)
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // absorb final_step ++ extras in one keccak, THEN draw). next_claim unused (sccl recomputes).
    next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, 26)
}

            function scl2_caches() {
            }
            function scl2_g0(alpha, a) -> acc { acc := a
    // CopyInExtensionField: [25] = 17
    acc := gate_copyinextensionfield(alpha, acc, 25)
    
    // CopyInExtensionField: [24] = 16
    acc := gate_copyinextensionfield(alpha, acc, 24)
    
    // CopyInExtensionField: [19] = 15
    acc := gate_copyinextensionfield(alpha, acc, 19)
    
    // CopyInExtensionField: [18] = 14
    acc := gate_copyinextensionfield(alpha, acc, 18)
    
    // AggregateLookupRationalPair: [22]/[23] + [20]/[21] = 12/13
    acc := gate_aggregatelookuprationalpair(alpha, acc, 22, 20, 23, 21)
    
    // CopyInExtensionField: [13] = 11
    acc := gate_copyinextensionfield(alpha, acc, 13)
    
    // CopyInExtensionField: [12] = 10
    acc := gate_copyinextensionfield(alpha, acc, 12)
    
    // AggregateLookupRationalPair: [16]/[17] + [14]/[15] = 8/9
    acc := gate_aggregatelookuprationalpair(alpha, acc, 16, 14, 17, 15)
    
    // CopyInExtensionField: [4] = 7
    acc := gate_copyinextensionfield(alpha, acc, 4)
    
    // CopyInExtensionField: [3] = 6
    acc := gate_copyinextensionfield(alpha, acc, 3)
    
    // AggregateLookupRationalPair: [7]/[8] + [5]/[6] = 4/5
    acc := gate_aggregatelookuprationalpair(alpha, acc, 7, 5, 8, 6)
    
    {  // LookupUnbalancedPairWithMaterializedBaseInputs: [9]/[10] + 1/(δ + [11]) = 2/3
        let den_out := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11))))), mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11))))), mload(P_PTR)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
            }
            function scl2_g1(alpha, a) -> acc { acc := a
    // MaskIntoIdentityProduct: [2]*[0] + (1-[0]) = 1
    acc := gate_maskintoidentityproduct(alpha, acc, 2, 0)
    
    // MaskIntoIdentityProduct: [1]*[0] + (1-[0]) = 0
    acc := gate_maskintoidentityproduct(alpha, acc, 1, 0)
    
            }
            function sccl2(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := 0
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 17))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 16))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 15))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 14))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 13))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 12))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 11))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 10))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 0))))
            }
function sumcheck_circuit_layer1(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl1(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc := 0
            mstore(CIRCUIT_PTR, ptr)
            scl1_caches()
            acc := scl1_g0(alpha, acc)
            acc := scl1_g1(alpha, acc)
    let rhs_scaled := mulmod(acc, eq_scale, mload(P_PTR))
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(mload(P_PTR), rhs_scaled)), mload(P_PTR)) { revert(0, 0) }

    
            // WRITEBACK claims for next layer (74 evals) + canonicity guard
                for { let wk := 0 } lt(wk, 74) { wk := add(wk, 1) } {
                    let cv := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk))))
                    if iszero(lt(cv, mload(P_PTR))) { revert(0, 0) }
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), cv)
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // absorb final_step ++ extras in one keccak, THEN draw). next_claim unused (sccl recomputes).
    {
            let base := mload(CIRCUIT_PTR)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            let bp := add(GKR_ABS_PTR(), 32)
            // absorb final_step ++ extras contiguously, then draw (soundness: batching depends on
            // the extra cache-dependency evals). ONE keccak of [seed || final_step || extras].
            calldatacopy(bp, add(base, mul(16, 0)), mul(16, 8))
            bp := add(bp, mul(16, 8))
            calldatacopy(bp, add(base, mul(16, 48)), mul(16, 26))
            bp := add(bp, mul(16, 26))
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
            calldatacopy(bp, add(base, mul(16, 8)), mul(16, 40))
            bp := add(bp, mul(16, 40))
            let s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR()))
            mstore(SEED_PTR(), s)
            s := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), s)
            next_alpha := mod(shr(128, s), mload(P_PTR))
            next_ptr := add(ptr, mul(16, 74))
            next_claim := 0
            }
}

            function scl1_caches() {
    {  // VectorizedLookup: (0 + 1[9]) + (0 + 1[10]) + (0 + 1[11]) + (0 + 0) + (0 + 0) + (0 + 0) + (0 + 0) + (0 + 0) + (0 + 0) + (0 + 1[8]) = Cache(0)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))))), add(0, 0)), add(0, 0)), add(0, 0)), add(0, 0)), add(0, 0)), add(0, 0)), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (0 + 1[13]) + (0 + 1[14]) + (0 + 1[15]) + (0 + 1[16]) + (0 + 1[17]) + (0 + 1[18]) + (0 + 1[19]) + (0 + 1[20]) + (0 + 0) + (0 + 1[12]) = Cache(1)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 12)))))), add(0, 0)), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 15)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 14)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 13))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (0 + 1[22]) + (0 + 1[23]) + (0 + 1[24]) + (0 + 1[25]) + (0 + 1[26]) + (0 + 1[27]) + (0 + 1[28]) + (0 + 1[29]) + (0 + 0) + (0 + 1[21]) = Cache(2)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))))), add(0, 0)), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 29)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (0 + 1[31]) + (0 + 1[32]) + (0 + 1[33]) + (0 + 1[34]) + (0 + 1[35]) + (0 + 1[36]) + (0 + 1[37]) + (0 + 1[38]) + (0 + 0) + (0 + 1[30]) = Cache(3)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 30)))))), add(0, 0)), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 38)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 37)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 36)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 35)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 34)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 33)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 32)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 31))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (0 + 1[40]) + (0 + 1[41]) + (0 + 1[42]) + (0 + 1[43]) + (0 + 1[44]) + (0 + 1[45]) + (0 + 1[46]) + (0 + 1[47]) + (0 + 0) + (0 + 1[39]) = Cache(4)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 39)))))), add(0, 0)), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)), mod(gate, mload(P_PTR)))
    }
            }
            function scl1_g0(alpha, a) -> acc { acc := a
    // CopyInExtensionField: [5] = 25
    acc := gate_copyinextensionfield(alpha, acc, 5)
    
    // CopyInExtensionField: [6] = 24
    acc := gate_copyinextensionfield(alpha, acc, 6)
    
    {  // LookupUnbalancedPairWithMaterializedVectorInputs: [72]/[73] + 1/(δ + Cache(4)) = 22/23
        let den_out := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 73)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)))), mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 72)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)))), mload(P_PTR)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 73)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedVectorInputs: 1/(δ+Cache(2)) + 1/(δ+Cache(3)) = 20/21
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedVectorInputs: 1/(δ+Cache(0)) + 1/(δ+Cache(1)) = 18/19
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    // CopyInExtensionField: [64] = 17
    acc := gate_copyinextensionfield(alpha, acc, 64)
    
    // CopyInExtensionField: [63] = 16
    acc := gate_copyinextensionfield(alpha, acc, 63)
    
    // AggregateLookupRationalPair: [67]/[68] + [65]/[66] = 14/15
    acc := gate_aggregatelookuprationalpair(alpha, acc, 67, 65, 68, 66)
    
    {  // LookupUnbalancedPairWithMaterializedBaseInputs: [69]/[70] + 1/(δ + [71]) = 12/13
        let den_out := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71))))), mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71))))), mload(P_PTR)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // CopyInBaseField: [7] = 11
        let gate := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7))))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    // AggregateLookupRationalPair: [50]/[51] + [48]/[49] = 9/10
    acc := gate_aggregatelookuprationalpair(alpha, acc, 50, 48, 51, 49)
    
    // AggregateLookupRationalPair: [54]/[55] + [52]/[53] = 7/8
    acc := gate_aggregatelookuprationalpair(alpha, acc, 54, 52, 55, 53)
    
            }
            function scl1_g1(alpha, a) -> acc { acc := a
    // AggregateLookupRationalPair: [58]/[59] + [56]/[57] = 5/6
    acc := gate_aggregatelookuprationalpair(alpha, acc, 58, 56, 59, 57)
    
    {  // LookupUnbalancedPairWithMaterializedBaseInputs: [60]/[61] + 1/(δ + [62]) = 3/4
        let den_out := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62))))), mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62))))), mload(P_PTR)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // TrivialProduct: [2]*[4] = 2
        let gate := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 4)))), mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // TrivialProduct: [1]*[3] = 1
        let gate := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 1)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // CopyInBaseField: [0] = 0
        let gate := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 0))))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
            }
            function sccl1(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := 0
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 25))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 24))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 23))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 22))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 21))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 20))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 19))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 18))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 17))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 16))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 15))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 14))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 13))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 12))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 11))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 10))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 0))))
            }
function sumcheck_circuit_layer0(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl0(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc := 0
            mstore(CIRCUIT_PTR, ptr)
            scl0_caches()
            // ── layer-0 max-quadratic gates: table-driven evaluation ──────────────────────
            // Each gate's value is Σ(constant + Σ coeff·col[a] + Σ coeff·col[a]·col[b]), summed
            // into gateval[gate_slot] and read back by the Horner chunk functions. Terms are stored
            // as packed records rather than unrolled code (a large bytecode saving). Record layout
            // (big-endian): [gate_slot:1][col_a:1]([col_b:1] for quadratic)[coeff:1|2|4|16]. Records
            // are grouped into buckets by (linear/quadratic, coeff sign, coeff byte-width) so each
            // loop below has one fixed stride; small negative coefficients store their magnitude and
            // are negated in-loop.
            // seed gateval[gate_slot] with each relation's nonzero constant term
            mstore(add(GKR_GATEVAL_PTR(), mul(32, 34)), 0x380000000000000000000000000)
            mstore(add(GKR_GATEVAL_PTR(), mul(32, 35)), 0x37ffe4000000000000000000000)
            mstore(add(GKR_GATEVAL_PTR(), mul(32, 86)), 0x7800000100000000)
            // packed term records, written 32 bytes at a time
            mstore(add(GKR_QTABLE_PTR(), 0), 0x221d01242b01242c01242d01242e01242f012430012431012432012433012434)
            mstore(add(GKR_QTABLE_PTR(), 32), 0x01243501243601243701243801243901243a01243b0124090124100125610127)
            mstore(add(GKR_QTABLE_PTR(), 64), 0x60042860012e5e01371201381101390b013a0a01425d01435c01445b01473704)
            mstore(add(GKR_QTABLE_PTR(), 96), 0x4738044b35044b3604532e01532f01533001533101542e01542f015430015431)
            mstore(add(GKR_QTABLE_PTR(), 128), 0x015f3a03603502603602603702603802603a09683a0269353369363369373369)
            mstore(add(GKR_QTABLE_PTR(), 160), 0x3833693a09713a01723505723605723705723805723a097b35057b36057b3705)
            mstore(add(GKR_QTABLE_PTR(), 192), 0x7b38057b3a097f35017f36017f37017f38017f3a087f3b03522e7800522f7800)
            mstore(add(GKR_QTABLE_PTR(), 224), 0x52307800523178002218000000e0000000000000000000000000221c06ffff20)
            mstore(add(GKR_QTABLE_PTR(), 256), 0x0000000000000000000000012318000000dfff2000000000000000000000231c)
            mstore(add(GKR_QTABLE_PTR(), 288), 0x06ffff2000e000000000000000000001552f0000000000000000000000016800)
            mstore(add(GKR_QTABLE_PTR(), 320), 0x0003565806ffffffffffffffffffffff00000001006401016301026201036101)
            mstore(add(GKR_QTABLE_PTR(), 352), 0x046001055f01065e01075d01085c01095b010a40010b3f010c3e010d3d010e3c)
            mstore(add(GKR_QTABLE_PTR(), 384), 0x010f1001100901113b01123a0113390114380115370116360117350118340119)
            mstore(add(GKR_QTABLE_PTR(), 416), 0x33011a32011b31011c30011d2f011e2e011f2d01202c01212b01221901281501)
            mstore(add(GKR_QTABLE_PTR(), 448), 0x3827013a2601433701443501443601475a04485a015715018009408010400064)
            mstore(add(GKR_QTABLE_PTR(), 480), 0x640101636301026262010361610104606001055f5f01065e5e01075d5d01085c)
            mstore(add(GKR_QTABLE_PTR(), 512), 0x5c01095b5b010a4040010b3f3f010c3e3e010d3d3d010e3c3c010f1010011009)
            mstore(add(GKR_QTABLE_PTR(), 544), 0x0901113b3b01123a3a0113393901143838011537370116363601173535011834)
            mstore(add(GKR_QTABLE_PTR(), 576), 0x3401193333011a3232011b3131011c3030011d2f2f011e2e2e011f2d2d01202c)
            mstore(add(GKR_QTABLE_PTR(), 608), 0x2c01212b2b01265f600126601701276016012835150128361501283715012838)
            mstore(add(GKR_QTABLE_PTR(), 640), 0x1501293f0901293f100129400901294010012a3f10012a4010022a5610042b3f)
            mstore(add(GKR_QTABLE_PTR(), 672), 0x09012b4009022b5609042c5e08012c0914012c1014012d5e07012d0913012d10)
            mstore(add(GKR_QTABLE_PTR(), 704), 0x13012f3e1001303e100131421001324209013341100134410901352909013529)
            mstore(add(GKR_QTABLE_PTR(), 736), 0x1001353c0901353c100135030901350310013628090136281001360209013602)
            mstore(add(GKR_QTABLE_PTR(), 768), 0x1001382710013a2609013b3a44013b3a48013b3a4c013b3a50013b3b44013b3b)
            mstore(add(GKR_QTABLE_PTR(), 800), 0x47013b3b4a013b3b51013c3a42013c3a46013c3a4a013c3a4e013c3b42013c3b)
            mstore(add(GKR_QTABLE_PTR(), 832), 0x49013c3b4c013c3b4f013d5d14013e5d13013f5c140140575b0141435c014156)
            mstore(add(GKR_QTABLE_PTR(), 864), 0x5b01433739014435390144363901453540014536400145405a01462935014629)
            mstore(add(GKR_QTABLE_PTR(), 896), 0x360146295a0146353e014635170146363e014636030146373e01463717014638)
            mstore(add(GKR_QTABLE_PTR(), 928), 0x3e0146381701472835014728360147285a014735160147360201473716014738)
            mstore(add(GKR_QTABLE_PTR(), 960), 0x160148384301493544014936440149374401493844014a2937014a353c014a35)
            mstore(add(GKR_QTABLE_PTR(), 992), 0x17014a363c014a3617014a373c014a3757014a3708014a383c014a3857014a38)
            mstore(add(GKR_QTABLE_PTR(), 1024), 0x08014b2837014b3516014b3616014b3756014b3707014b3856014b3807014c32)
            mstore(add(GKR_QTABLE_PTR(), 1056), 0x14014d3213014e3206014f320501503208015132070152292b0152292d01522b)
            mstore(add(GKR_QTABLE_PTR(), 1088), 0x3d01522b0301522b0801522c3d01522c0801522c1401522d3d01522d1701522e)
            mstore(add(GKR_QTABLE_PTR(), 1120), 0x3d01522e5701522f3d01522f570152303d015230570152313d01523157015234)
            mstore(add(GKR_QTABLE_PTR(), 1152), 0x3d0152343e01523403015234080152340f0153282b0153282d01532b0201532b)
            mstore(add(GKR_QTABLE_PTR(), 1184), 0x0701532c0701532c1301532d1601532e5601532f560153305601533156015334)
            mstore(add(GKR_QTABLE_PTR(), 1216), 0x02015334070153340e01552e0201552e0701552f020155301301553113015602)
            mstore(add(GKR_QTABLE_PTR(), 1248), 0x070157151501583a5101593a50015a3a4f015a3b51015b3a4e015b3b50015c2a)
            mstore(add(GKR_QTABLE_PTR(), 1280), 0x3a015c3b4f015d283a015d351a015d361a015d371a015d381a015d3a41015d3b)
            mstore(add(GKR_QTABLE_PTR(), 1312), 0x4e015e3540015e3640015e3740015e3840015e3b41015f3559015f3659015f37)
            mstore(add(GKR_QTABLE_PTR(), 1344), 0x59015f385901602a3b01613a4d01623a4c01633a4b01633b4d01643a4a01643b)
            mstore(add(GKR_QTABLE_PTR(), 1376), 0x4c01652a3a01653b4b0166283a01663a4101663b4a0167354301673643016737)
            mstore(add(GKR_QTABLE_PTR(), 1408), 0x430167384301673a5301673b4101673b5501682a3510682a3610682a3710682a)
            mstore(add(GKR_QTABLE_PTR(), 1440), 0x381068353d0468354108683542026835450168363d0468364108683642026836)
            mstore(add(GKR_QTABLE_PTR(), 1472), 0x450168373d0468374108683742026837450168383d0468384108683842026838)
            mstore(add(GKR_QTABLE_PTR(), 1504), 0x4501683b5301692a3b016a3a49016b3a48016c3a47016c3b49016d3a46016d3b)
            mstore(add(GKR_QTABLE_PTR(), 1536), 0x48016e2a3a016e3b47016f283a016f3a41016f3b460170293b01703545017036)
            mstore(add(GKR_QTABLE_PTR(), 1568), 0x4501703745017038450171354401713644017137440171384401722a3b01733a)
            mstore(add(GKR_QTABLE_PTR(), 1600), 0x4501743a4401753a4301753b4501763a4201763b4401772a3a01773b43017828)
            mstore(add(GKR_QTABLE_PTR(), 1632), 0x3a01783a4101783b420179283b0179354201793642017937420179384201793a)
            mstore(add(GKR_QTABLE_PTR(), 1664), 0x5201793b54017a3503017a3603017a3703017a3803017a3b52017b2a3b017c3a)
            mstore(add(GKR_QTABLE_PTR(), 1696), 0x41017c145e017d3541017d3641017d3741017d3841017d3b41017d135e017e29)
            mstore(add(GKR_QTABLE_PTR(), 1728), 0x3b017e3556017e3557017e3656017e3657017e3756017e3757017e3856017e38)
            mstore(add(GKR_QTABLE_PTR(), 1760), 0x57017e3a54017e415e017f155e2280094201801042013b3a4501003b3a490100)
            mstore(add(GKR_QTABLE_PTR(), 1792), 0x3b3a4d01003b3a5101003b3b4501003b3b4801003b3b4b01003b3b4e01003c3a)
            mstore(add(GKR_QTABLE_PTR(), 1824), 0x4301003c3a4701003c3a4b01003c3a4f01003c3b4301003c3b4601003c3b4d01)
            mstore(add(GKR_QTABLE_PTR(), 1856), 0x003c3b500100552e0300010000552e0800010000552f03000100005530140001)
            mstore(add(GKR_QTABLE_PTR(), 1888), 0x00005531140001000056020800010000560307000100007e425e000100008009)
            mstore(add(GKR_QTABLE_PTR(), 1920), 0x3e0001000080103e0001000023181806ffffffffe40000000000000000000123)
            mstore(add(GKR_QTABLE_PTR(), 1952), 0x181c00000000003800000000000000000000231c1c06ffffffffe40000000000)
            mstore(add(GKR_QTABLE_PTR(), 1984), 0x0000000001552e4006fffffffffffffffffffffe1ffffffd552f4006ffffffff)
            mstore(add(GKR_QTABLE_PTR(), 2016), 0xfffffffffffffe1ffffffd56303e06ffffffffffffff87ffffff000000015630)
            mstore(add(GKR_QTABLE_PTR(), 2048), 0x3f06ffffffffffffff0ffffffe0000000156304006fffffffffffffe1ffffffc)
            mstore(add(GKR_QTABLE_PTR(), 2080), 0x0000000156304206ffffffffffffffffff87ffffff000156313e06ffffffffff)
            mstore(add(GKR_QTABLE_PTR(), 2112), 0xffff87ffffff0000000156313f06ffffffffffffff0ffffffe00000001563140)
            mstore(add(GKR_QTABLE_PTR(), 2144), 0x06fffffffffffffe1ffffffc0000000156314206ffffffffffffffffff87ffff)
            mstore(add(GKR_QTABLE_PTR(), 2176), 0xff000156310e0000000000000000000000010000000056310f00000000000000)
            mstore(add(GKR_QTABLE_PTR(), 2208), 0x000001000000000000560308000000000000000000000001000000005e3a5300)
            mstore(add(GKR_QTABLE_PTR(), 2240), 0x0700000000000000000000000000005e3a0306f9000000000000000000000000)
            mstore(add(GKR_QTABLE_PTR(), 2272), 0x00015e3b55000700000000000000000000000000005e3b0806f9000000000000)
            mstore(add(GKR_QTABLE_PTR(), 2304), 0x00000000000000015f3b53000700000000000000000000000000005f3b0306f9)
            mstore(add(GKR_QTABLE_PTR(), 2336), 0x0000000000000000000000000001703a52000700000000000000000000000000)
            mstore(add(GKR_QTABLE_PTR(), 2368), 0x00703a0206f90000000000000000000000000001703b54000700000000000000)
            mstore(add(GKR_QTABLE_PTR(), 2400), 0x00000000000000703b0706f90000000000000000000000000001713b52000700)
            mstore(add(GKR_QTABLE_PTR(), 2432), 0x00000000000000000000000000713b0206f90000000000000000000000000001)
            mstore(add(GKR_QTABLE_PTR(), 2464), 0x7d3a54000700000000000000000000000000007d3a0706f90000000000000000)
            mstore(add(GKR_QTABLE_PTR(), 2496), 0x000000000001242b1501242c1501242d1501242e1501242f1501243015012431)
            mstore(add(GKR_QTABLE_PTR(), 2528), 0x1501243215012433150124341501243515012436150124371501243815012439)
            mstore(add(GKR_QTABLE_PTR(), 2560), 0x1501243a1501243b15012409150124101501252b1501252c1501252d1501252e)
            mstore(add(GKR_QTABLE_PTR(), 2592), 0x1501252f15012530150125311501253215012533150125341501253515012536)
            mstore(add(GKR_QTABLE_PTR(), 2624), 0x15012537150125381501253a1501253b1501250915012510150126601b012760)
            mstore(add(GKR_QTABLE_PTR(), 2656), 0x1a012a1011012b090a012c5e14012c0809012c0810012d5e13012d0709012d07)
            mstore(add(GKR_QTABLE_PTR(), 2688), 0x10012e3e09013110120132090b013310110134090a0135090b01351012013609)
            mstore(add(GKR_QTABLE_PTR(), 2720), 0x0a0136101101371012013810110139090b013a090a013b3a14013b3b14013c3a)
            mstore(add(GKR_QTABLE_PTR(), 2752), 0x13013c3b1301405b1401415b1301415c13014235390142363901423739014238)
            mstore(add(GKR_QTABLE_PTR(), 2784), 0x390146351b0146361b0146371b0146381b014735590147365901473759014738)
            mstore(add(GKR_QTABLE_PTR(), 2816), 0x590149293701493508014936080149370801493808014a3557014a3657014a37)
            mstore(add(GKR_QTABLE_PTR(), 2848), 0x03014a3803014b3556014b3656014b3702014b380201522b1401522c0301522d)
            mstore(add(GKR_QTABLE_PTR(), 2880), 0x1401522e1401522f1401523014015231140152341401532b1301532c0201532d)
            mstore(add(GKR_QTABLE_PTR(), 2912), 0x1301532e1301532f1301533013015331130153341301542e3c01542f3c015430)
            mstore(add(GKR_QTABLE_PTR(), 2944), 0x3c0154313c01552e1301552f0701552f13015530580155315801275f60000100)
            mstore(add(GKR_QTABLE_PTR(), 2976), 0x00353d0900010000353d1000010000363c0900010000363c100001000046353f)
            mstore(add(GKR_QTABLE_PTR(), 3008), 0x0001000046363f0001000046373f0001000046383f0001000047353e00010000)
            mstore(add(GKR_QTABLE_PTR(), 3040), 0x47363e0001000047373e0001000047383e000100004a353d000100004a363d00)
            mstore(add(GKR_QTABLE_PTR(), 3072), 0x0100004a373d000100004a383d000100004b353c000100004b363c000100004b)
            mstore(add(GKR_QTABLE_PTR(), 3104), 0x373c000100004b383c00010000522b3c00010000522c3c00010000522d3c0001)
            mstore(add(GKR_QTABLE_PTR(), 3136), 0x0000522e3c00010000522f3c0001000052303c0001000052313c000100005234)
            mstore(add(GKR_QTABLE_PTR(), 3168), 0x3c0001000052343f00010000532b3d00010000532c3d00010000532d3d000100)
            mstore(add(GKR_QTABLE_PTR(), 3200), 0x00532e3d00010000532f3d0001000053303d0001000053313d0001000053343d)
            mstore(add(GKR_QTABLE_PTR(), 3232), 0x0001000053343e00010000552e3e78000001552e3ff0000002552e1400010000)
            mstore(add(GKR_QTABLE_PTR(), 3264), 0x552f3e78000001552f3ff0000002552f0800010000552f140001000056304178)
            mstore(add(GKR_QTABLE_PTR(), 3296), 0x0000015631417800000100000000000000000000000000000000000000000000)
            // accumulate every term into gateval[gate_slot], one loop per bucket
            {
            let modulus := P
            let col_base := mload(CIRCUIT_PTR) // calldata base of the column at-point evals
            let gateval := GKR_GATEVAL_PTR()
            // linear    terms, coeff  1B positive  (72 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 0) let rec_end := add(rec_ptr, 216)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 3) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(232, rec), 0xff), shr(128, calldataload(add(col_base, mul(16, byte(1, rec))))), modulus), modulus))
            } }
            // linear    terms, coeff  2B positive  (4 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 216) let rec_end := add(rec_ptr, 16)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 4) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(224, rec), 0xffff), shr(128, calldataload(add(col_base, mul(16, byte(1, rec))))), modulus), modulus))
            } }
            // linear    terms, coeff 16B canonical (6 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 232) let rec_end := add(rec_ptr, 108)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 18) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(112, rec), MASK), shr(128, calldataload(add(col_base, mul(16, byte(1, rec))))), modulus), modulus))
            } }
            // linear    terms, coeff  1B negative  (46 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 340) let rec_end := add(rec_ptr, 138)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 3) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(sub(modulus, and(shr(232, rec), 0xff)), shr(128, calldataload(add(col_base, mul(16, byte(1, rec))))), modulus), modulus))
            } }
            // quadratic terms, coeff  1B positive  (326 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 478) let rec_end := add(rec_ptr, 1304)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 4) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(224, rec), 0xff), mulmod(shr(128, calldataload(add(col_base, mul(16, byte(1, rec))))), shr(128, calldataload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff  2B positive  (16 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 1782) let rec_end := add(rec_ptr, 80)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 5) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(216, rec), 0xffff), mulmod(shr(128, calldataload(add(col_base, mul(16, byte(1, rec))))), shr(128, calldataload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff  4B positive  (10 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 1862) let rec_end := add(rec_ptr, 70)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 7) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(200, rec), 0xffffffff), mulmod(shr(128, calldataload(add(col_base, mul(16, byte(1, rec))))), shr(128, calldataload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff 16B canonical (30 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 1932) let rec_end := add(rec_ptr, 570)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 19) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(104, rec), MASK), mulmod(shr(128, calldataload(add(col_base, mul(16, byte(1, rec))))), shr(128, calldataload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff  1B negative  (117 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 2502) let rec_end := add(rec_ptr, 468)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 4) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(sub(modulus, and(shr(224, rec), 0xff)), mulmod(shr(128, calldataload(add(col_base, mul(16, byte(1, rec))))), shr(128, calldataload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff  4B negative  (48 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 2970) let rec_end := add(rec_ptr, 336)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 7) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(sub(modulus, and(shr(200, rec), 0xffffffff)), mulmod(shr(128, calldataload(add(col_base, mul(16, byte(1, rec))))), shr(128, calldataload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            }

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
    let rhs_scaled := mulmod(acc, eq_scale, mload(P_PTR))
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(mload(P_PTR), rhs_scaled)), mload(P_PTR)) { revert(0, 0) }

    
            // canonicity guard for the base-layer claims_batch absorb: 114 at-point evals from
            // calldata; require each < P so the absorbed transcript bytes are canonical
                for { let wk := 0 } lt(wk, 114) { wk := add(wk, 1) } {
                    if iszero(lt(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk)))), mload(P_PTR))) { revert(0, 0) }
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // absorb final_step ++ extras in one keccak, THEN draw). next_claim unused (sccl recomputes).
    {
            let base := mload(CIRCUIT_PTR)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            let bp := add(GKR_ABS_PTR(), 32)
            // absorb final_step ++ extras contiguously, then draw (soundness: batching depends on
            // the extra cache-dependency evals). ONE keccak of [seed || final_step || extras].
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
            calldatacopy(bp, add(base, mul(16, 0)), mul(16, 2))
            bp := add(bp, mul(16, 2))
            calldatacopy(bp, add(base, mul(16, 4)), mul(16, 1))
            bp := add(bp, mul(16, 1))
            calldatacopy(bp, add(base, mul(16, 12)), mul(16, 2))
            bp := add(bp, mul(16, 2))
            calldatacopy(bp, add(base, mul(16, 104)), mul(16, 10))
            bp := add(bp, mul(16, 10))
            let s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR()))
            mstore(SEED_PTR(), s)
            s := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), s)
            next_alpha := mod(shr(128, s), mload(P_PTR))
            next_ptr := add(ptr, mul(16, 114))
            next_claim := 0
            }
}

            function scl0_caches() {
    {  // MemoryTuple: (γ + 0 + α[4] + α²0 + α³(0 + [0]) + α⁴[1] + α⁵[2] + α⁶[3]) = Cache(0)
        let gate := add(gkr_memrel_compress_low(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 4)))), 0), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 0))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 1)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + [9] + α[10] + α²[11] + α³(0 + [5]) + α⁴[6] + α⁵[7] + α⁶[8]) = Cache(1)
        let gate := add(gkr_memrel_compress_low(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11))))), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 5))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 6)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + 0 + α[4] + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[2] + α⁶[3]) = Cache(2)
        let gate := add(gkr_memrel_compress_low(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 4)))), 0), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + [9] + α[10] + α²[11] + α³(1 + [24]) + α⁴[25] + α⁵[7] + α⁶[8]) = Cache(3)
        let gate := add(gkr_memrel_compress_low(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11))))), gkr_memrel_compress_high(add(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + [16] + α[17] + α²[18] + α³(0 + [12]) + α⁴[13] + α⁵[14] + α⁶[15]) = Cache(4)
        let gate := add(gkr_memrel_compress_low(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18))))), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 12))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 13)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 14)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 15))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + 2 + α0 + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[22] + α⁶[23]) = Cache(5)
        let gate := add(gkr_memrel_compress_low(2, 0, 0), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 5)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + [16] + α[17] + α²[18] + α³(2 + [24]) + α⁴[25] + α⁵[19] + α⁶[20]) = Cache(6)
        let gate := add(gkr_memrel_compress_low(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18))))), gkr_memrel_compress_high(add(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 6)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + 2 + α0 + α²0 + α³(0 + [28]) + α⁴[29] + α⁵[26] + α⁶[27]) = Cache(7)
        let gate := add(gkr_memrel_compress_low(2, 0, 0), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 29)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 7)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: 0 + -1[24] + 1[0] + 2^19[98] = Cache(8)
        let gate := add(0, add(add(mulmod(sub(mload(P_PTR), 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), mload(P_PTR)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 0))))), mulmod(524288, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 98)))), mload(P_PTR))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 8)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: 2^19 + -1[25] + 1[1] + -1[98] = Cache(9)
        let gate := add(524288, add(add(mulmod(sub(mload(P_PTR), 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), mload(P_PTR)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 1))))), mulmod(sub(mload(P_PTR), 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 98)))), mload(P_PTR))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 9)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: -1 + -1[24] + 1[5] + 2^19[99] = Cache(10)
        let gate := add(sub(mload(P_PTR), 1), add(add(mulmod(sub(mload(P_PTR), 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), mload(P_PTR)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 5))))), mulmod(524288, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 99)))), mload(P_PTR))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 10)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: 2^19 + -1[25] + 1[6] + -1[99] = Cache(11)
        let gate := add(524288, add(add(mulmod(sub(mload(P_PTR), 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), mload(P_PTR)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 6))))), mulmod(sub(mload(P_PTR), 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 99)))), mload(P_PTR))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 11)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: -2 + -1[24] + 1[12] + 2^19[100] = Cache(12)
        let gate := add(sub(mload(P_PTR), 2), add(add(mulmod(sub(mload(P_PTR), 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), mload(P_PTR)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 12))))), mulmod(524288, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 100)))), mload(P_PTR))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 12)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: 2^19 + -1[25] + 1[13] + -1[100] = Cache(13)
        let gate := add(524288, add(add(mulmod(sub(mload(P_PTR), 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), mload(P_PTR)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 13))))), mulmod(sub(mload(P_PTR), 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 100)))), mload(P_PTR))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 13)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (0 + 1[22]) + (0 + 1[23]) + (0 + 1[4]) + (0 + 1[38]) + (0 + 1[39]) + (0 + 1[40]) + (0 + 1[41]) + (0 + 1[42]) + (0 + 1[43] + 2[44] + 2^2[45] + 2^3[46] + 2^4[47] + 2^5[48] + 2^6[49] + 2^7[50] + 2^8[51] + 2^9[52] + 2^10[53] + 2^11[54] + 2^12[55] + 2^13[56] + 2^14[57] + 2^15[58] + 2^16[59] + 2^17[9] + 2^18[16]) + (46 + 0) = Cache(14)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(46, 0)), add(0, add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), mload(P_PTR))), mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), mload(P_PTR))), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), mload(P_PTR))), mulmod(16, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), mload(P_PTR))), mulmod(32, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), mload(P_PTR))), mulmod(64, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), mload(P_PTR))), mulmod(128, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mload(P_PTR))), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), mload(P_PTR))), mulmod(512, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), mload(P_PTR))), mulmod(1024, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mload(P_PTR))), mulmod(2048, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mload(P_PTR))), mulmod(4096, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mload(P_PTR))), mulmod(8192, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mload(P_PTR))), mulmod(16384, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), mload(P_PTR))), mulmod(32768, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mload(P_PTR))), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mload(P_PTR))), mulmod(131072, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mload(P_PTR))), mulmod(262144, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mload(P_PTR))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 39)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 38)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 4)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))))), add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 14)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookupSetup: β⁰[104] + β¹[105] + β²[106] + β³[107] + β⁴[108] + β⁵[109] + β⁶[110] + β⁷[111] + β⁸[112] + β⁹[113] = Cache(15)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 113))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 112))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 111))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 110))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 109))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 108))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 107))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 106))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 105))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 104)))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 15)), mod(gate, mload(P_PTR)))
    }
    {  // RangeCheck16Bits: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8])(1 - r[7])(1 - r[6])(1 - r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = Cache(16)
        let gate := gkr_virtual_poly_rangecheck(16)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)), mod(gate, mload(P_PTR)))
    }
    {  // RangeCheckTimestamp: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8] + 2^16 r[7] + 2^17 r[6] + 2^18 r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = Cache(17)
        let gate := gkr_virtual_poly_rangecheck(19)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)), mod(gate, mload(P_PTR)))
    }
    {  // InitsAndTeardownsLow: 4(2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10]) = Cache(18)
        let gate := mul(4, gkr_virtual_poly_compose_vars(14, 0)) // u32 word-aligned
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18)), mod(gate, mload(P_PTR)))
    }
    {  // InitsAndTeardownsHigh: 2^0 r[9] + 2^1 r[8] + 2^2 r[7] + 2^3 r[6] + 2^4 r[5] + 2^5 r[4] + 2^6 r[3] + 2^7 r[2] + 2^8 r[1] + 2^9 r[0] = Cache(19)
        let gate := gkr_virtual_poly_compose_vars(8, 14)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19)), mod(gate, mload(P_PTR)))
    }
            }
            function scl0_g0(alpha, a) -> acc { acc := a
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 0 } lt(s, 12) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g1(alpha, a) -> acc { acc := a
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 12 } lt(s, 24) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g2(alpha, a) -> acc { acc := a
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 24 } lt(s, 36) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g3(alpha, a) -> acc { acc := a
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 36 } lt(s, 48) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g4(alpha, a) -> acc { acc := a
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 48 } lt(s, 60) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g5(alpha, a) -> acc { acc := a
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 60 } lt(s, 72) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g6(alpha, a) -> acc { acc := a
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 72 } lt(s, 84) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g7(alpha, a) -> acc { acc := a
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 84 } lt(s, 88) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

    {  // LookupWithCachedDensAndSetup: (([21])·((Cache(15))+δ) − ([103])·((Cache(14))+δ)) / (((Cache(14))+δ)((Cache(15))+δ)) = 72/73
        let bg := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 14))))
        let dg := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 15))))
        let den_out := mulmod(bg, dg, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), dg, mload(P_PTR)), sub(mul(2, mload(P_PTR)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 103)))), bg, mload(P_PTR))))
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // CopyInBaseField: Cache(13) = 71
        let gate := mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 13)))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+Cache(11)) + 1/(δ+Cache(12)) = 69/70
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 11))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 12))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+Cache(9)) + 1/(δ+Cache(10)) = 67/68
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 9))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 10))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[29]) + 1/(δ+Cache(8)) = 65/66
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 29)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 8))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupFromMaterializedBaseInputWithSetup: 1/(δ + [28]) - [102]/(δ + Cache(17)) = 63/64
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28))))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)))), mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)))), sub(mload(P_PTR), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 102)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28))))), mload(P_PTR))))
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // CopyInBaseField: [27] = 62
        let gate := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27))))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[18]) + 1/(δ+[26]) = 60/61
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
            }
            function scl0_g8(alpha, a) -> acc { acc := a
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[11]) + 1/(δ+[17]) = 58/59
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[89]) + 1/(δ+[10]) = 56/57
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 89)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[66]) + 1/(δ+[23]) = 54/55
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[20]) + 1/(δ+[65]) = 52/53
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[87]) + 1/(δ+[19]) = 50/51
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupFromMaterializedBaseInputWithSetup: 1/(δ + [86]) - [101]/(δ + Cache(16)) = 48/49
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86))))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)))), mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)))), sub(mload(P_PTR), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 101)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86))))), mload(P_PTR))))
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 88 } lt(s, 94) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g9(alpha, a) -> acc { acc := a
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 94 } lt(s, 106) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g10(alpha, a) -> acc { acc := a
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 106 } lt(s, 118) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g11(alpha, a) -> acc { acc := a
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 118 } lt(s, 129) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[0]<<8)) + α³[32] + α⁴[33] + α⁵[30] + α⁶[31]) * (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[1]<<8)) + α³[36] + α⁴[37] + α⁵[34] + α⁶[35]) = 6
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR(), mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))), mload(P_PTR)))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(8, gkr_inits_teardowns_topbits(396))), mload(P_PTR)), gkr_memrel_compress_high(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 32)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 33)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 30)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 31))))))) // for memrel we collect
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(8, gkr_inits_teardowns_topbits(400))), mload(P_PTR)), gkr_memrel_compress_high(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 36)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 37)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 34)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 35))))))) // for memrel we collect
        let gate := mulmod(lhs, rhs, mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
            }
            function scl0_g12(alpha, a) -> acc { acc := a
    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[0]<<8)) + 0) * (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[1]<<8)) + 0) = 5
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR(), mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))), mload(P_PTR)))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(8, gkr_inits_teardowns_topbits(396))), mload(P_PTR)), 0)) // for memrel we collect
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(8, gkr_inits_teardowns_topbits(400))), mload(P_PTR)), 0)) // for memrel we collect
        let gate := mulmod(lhs, rhs, mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // InitialGrandProductFromCaches: Cache(6)*Cache(7) = 4
        let gate := mulmod(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 6))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 7))), mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // InitialGrandProductFromCaches: Cache(4)*Cache(5) = 3
        let gate := mulmod(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 5))), mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // InitialGrandProductFromCaches: Cache(2)*Cache(3) = 2
        let gate := mulmod(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3))), mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // InitialGrandProductFromCaches: Cache(0)*Cache(1) = 1
        let gate := mulmod(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1))), mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // CopyInBaseField: [21] = 0
        let gate := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21))))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
            }
            function sccl0(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := 0
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := mulmod(claim, alpha, mload(P_PTR))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 73))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 72))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 71))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 70))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 69))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 68))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 67))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 66))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 65))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 64))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 63))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 62))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 61))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 60))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 59))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 58))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 57))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 56))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 55))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 54))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 53))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 52))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 51))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 50))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 49))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 48))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 47))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 46))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 45))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 44))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 43))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 42))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 41))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 40))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 39))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 38))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 37))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 36))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 35))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 34))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 33))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 32))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 31))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 30))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 29))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 28))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 27))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 26))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 25))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 24))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 23))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 22))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 21))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 20))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 19))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 18))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 17))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 16))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 15))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 14))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 13))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 12))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 11))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 10))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, 0))))
            }
function sumcheck_rounds_circuit(ptr, claim) -> next_ptr, next_claim, eq_scale {
    // NB: need to inline __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS unfortunately
    eq_scale := 1
    let modulus := mload(P_PTR) // hoisted: DUP per use instead of re-mload every round
    for { let i := 0 } lt(i, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS) { i := add(i, 1) } {
        let w0 := calldataload(ptr)
        let w1 := calldataload(add(ptr, 32))
        let c0 := shr(128, w0)
        let c1 := and(w0, MASK)
        let c2 := shr(128, w1)
        let c3 := and(w1, MASK)
        let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, modulus)
        let r := transcript_4to1_dual(w0, w1, modulus) // before-check draw is intentional; see HEURISTICS.md
        // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
        if mod(add(claim, sub(modulus, g0g1_scaled)), modulus) { revert(0, 0) }
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
function transcriptNTo1(ptr, input_elements) -> alpha {
    let input_bytes := mul(input_elements, 16)
    calldatacopy(add(SEED_PTR(), 32), ptr, input_bytes)
    let seed := keccak256(SEED_PTR(), add(32, input_bytes)) // absorb evals
    mstore(SEED_PTR(), seed)
    seed := keccak256(SEED_PTR(), 32)                       // draw (the mirror draws a fresh el)
    mstore(SEED_PTR(), seed)
    alpha := mod(shr(128, seed), mload(P_PTR))                         // batching is a field element mod P
}
function sumcheck_claims_batch(ptr, points) -> next_ptr, next_claim, next_alpha {
    let is_odd := mod(points, 2)
    if is_odd {
        next_claim := shr(128, calldataload(add(ptr, mul(16, sub(points, 1)))))
    }
    next_alpha := transcriptNTo1(ptr, points)
    let even_points := sub(points, is_odd)
    let pairs := shr(1, even_points)
    for { let pair := sub(pairs, 1) } lt(pair, pairs) { pair := sub(pair, 1) } {
        let word := calldataload(add(ptr, mul(pair, 32)))
        let el1 := and(MASK, word)
        let el0 := shr(128, word)
        next_claim := add(mulmod(next_claim, next_alpha, mload(P_PTR)), el1)
        next_claim := add(mulmod(next_claim, next_alpha, mload(P_PTR)), el0)
    }
    next_ptr := add(ptr, mul(16, points))
}

function gkr_memrel_compress(address_space, addr_low, addr_high, ts_low, ts_high, val_low, val_high) -> compressed {
    compressed := add(mload(add(MEMORY_CHALLS_PTR(), 192)), address_space)
    compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR()), addr_low, mload(P_PTR)))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 32)), addr_high, mload(P_PTR)))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 64)), ts_low, mload(P_PTR)))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 96)), ts_high, mload(P_PTR)))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 128)), val_low, mload(P_PTR)))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 160)), val_high, mload(P_PTR)))
}

// Fold five generic lookup tuple columns into an existing Horner accumulator.
// A single helper that took all c0..c9 made solc materialize all ten columns
// at the call boundary and failed stack allocation. Splitting the fold into
// two five-column calls keeps each call boundary small while still supporting
// arbitrary linrel_to_calldata_inner() output for every column.
function gkr_lookrel_compress_half(acc, c0, c1, c2, c3, c4) -> acc_next {
    acc_next := add(mulmod(acc, mload(LOGUP_CHALLS_PTR()), mload(P_PTR)), c4)
    acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), mload(P_PTR)), c3)
    acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), mload(P_PTR)), c2)
    acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), mload(P_PTR)), c1)
    acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), mload(P_PTR)), c0)
}
// One β-Horner step: acc·β + c. Callers chain ten of these (see lookrel_horner)
// instead of one 5-arg compress_half, keeping every call boundary at 2 args so the
// enclosing cache/gate function stays inside the EVM stack limit.
function gkr_lookrel_step(acc, c) -> acc_next {
    acc_next := add(mulmod(acc, mload(LOGUP_CHALLS_PTR()), mload(P_PTR)), c)
}

// Split memrel into a 3-arg low + 4-arg high, composed by the caller as
// add(low(...), high(...)). A single 7-arg gkr_memrel_compress forced solc to
// materialize all 7 expression-args at the call boundary, running the enclosing
// cache function 1 slot too deep (same failure the lookrel split above avoids).
function gkr_memrel_compress_low(address_space, addr_low, addr_high) -> compressed {
    compressed := add(mload(add(MEMORY_CHALLS_PTR(), 192)), address_space)
    compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR()), addr_low, mload(P_PTR)))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 32)), addr_high, mload(P_PTR)))
}
function gkr_memrel_compress_high(ts_low, ts_high, val_low, val_high) -> compressed {
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 64)), ts_low, mload(P_PTR)))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 96)), ts_high, mload(P_PTR)))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 128)), val_low, mload(P_PTR)))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 160)), val_high, mload(P_PTR)))
}
// Reads one inits/teardowns `top_bits` u32 from the transcript preimage (little-endian,
// at absolute calldata `byteoff`). These are the RAM-set base chunk indices absorbed into
// Fiat-Shamir, so a mismatching value breaks the transcript — safe to read from calldata.
function gkr_inits_teardowns_topbits(byteoff) -> v {
    let w := calldataload(byteoff)
    v := add(add(byte(0, w), shl(8, byte(1, w))), add(shl(16, byte(2, w)), shl(24, byte(3, w))))
}

// Plain VARIABLE order (LSB binding): index bit k pairs with point coordinate k.
// compose_vars sums 2^k * point[skip + k] for k in 0..len (Horner from the top
// coordinate down); zero_vars forces the HIGHEST `len` coordinates to zero —
// both mirror the CPU generator's plain-order closed forms.
function gkr_virtual_poly_compose_vars(len, skip) -> eval {
    for { let i := add(skip, len) } gt(i, skip) { } {
        i := sub(i, 1)
        eval := add(mul(eval, 2), mload(add(POINT_PTR(), mul(i, 32))))
    }
}
function gkr_virtual_poly_zero_vars(len) -> eval {
    eval := 1
    let n := __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS
    for { let i := sub(n, len) } lt(i, n) { i := add(i, 1) } {
        eval := mulmod(eval, add(1, sub(mul(2, mload(P_PTR)), mload(add(POINT_PTR(), mul(i, 32))))), mload(P_PTR))
    }
}
function gkr_virtual_poly_rangecheck(width) -> eval {
    eval := mulmod(gkr_virtual_poly_compose_vars(width, 0), gkr_virtual_poly_zero_vars(sub(__TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS, width)), mload(P_PTR))
}

function gate_calldataload(idx) -> load {
    load := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, idx))))
}
function gate_mload(idx) -> load {
    load := mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, idx)))
}
function pointcheck_update(acc, alpha, gate) -> next_acc {
    next_acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
}
function logup_pointcheck_update(acc, alpha, num_out, den_out) -> next_acc {
    acc := pointcheck_update(acc, alpha, den_out)
    next_acc := pointcheck_update(acc, alpha, num_out)
}
function u128_neg(input) -> neg_input {
    neg_input := sub(mul(2, mload(P_PTR)), input)
}

// 3
function gate_aggregatelookuprationalpair(alpha, acc, num1_idx, num2_idx, den1_idx, den2_idx) -> next_acc {
    let num1 := gate_calldataload(num1_idx)
    let num2 := gate_calldataload(num2_idx)
    let den1 := gate_calldataload(den1_idx)
    let den2 := gate_calldataload(den2_idx)
    let den_out := mulmod(den1, den2, mload(P_PTR))
    let num_out := add(mulmod(num1, den2, mload(P_PTR)), mulmod(num2, den1, mload(P_PTR)))
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
    // let gate := add(mulmod(input, mask, mload(P_PTR)), add(1, neg_mask))
    let neg_one := sub(mload(P_PTR), 1)
    let gate := add(mulmod(mask, add(input, neg_one), mload(P_PTR)), 1)
    next_acc := pointcheck_update(acc, alpha, gate)
}

        // Circuit sumcheck: run every circuit layer from the output layer (highest index,
        // reads the dim-reduce output GKR_CLAIMS_PTR) down to layer 0. The call sequence is
        // generated from the artifact's layer count so it can't drift when the circuit gains
        // or loses a layer — see gkr_circuit_layer_calls in the generator.
        function gkr_circuit(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
            ptr, claim,
            alpha := sumcheck_circuit_layer4(ptr, claim, alpha)
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
        // mirrors whir.sol: [seed:32][batching:16][opening:16][z:__TEMPLATE_WHIR_Z_COORDS*16]
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
        // coords — a 4-var multilinear eval → single claim. LSB binding: adjacent evals
        // differ in pack-index bit 0, which pairs with e0, so the coords apply FORWARD
        // (mirrors the prover's merge_claims).
        function whir_fold16(cdbase, count, e0, e1, e2, e3) -> v {
            let sc := add(GKR_ABS_PTR(), 384)
            for { let i := 0 } lt(i, 16) { i := add(i, 1) } {
                let val := 0
                if lt(i, count) {
                val := shr(128, calldataload(add(cdbase, mul(16, i)))) }
                mstore(add(sc, mul(32, i)), val)
            }
            whir_foldhalf(sc, 16, e0)
            whir_foldhalf(sc, 8, e1)
            whir_foldhalf(sc, 4, e2)
            whir_foldhalf(sc, 2, e3)
            v := mload(sc)
        }

        // GKR→WHIR handoff: draw the 4 packing coords, merge the base-layer claims (mem++wit
        // 104→7, setup 10→1), draw the WHIR batching challenge (PoW nonce=0), form the batched
        // opening, and mark_gkr_verified(keccak(preimage)) with preimage
        //   [seed:32][batching:16][opening:16][z = base_z(22) ++ extra(4) : 26·16][caps:2·CAP·32]
        // (the pack index occupies the HIGH bits of the packed enumeration, so under LSB
        // binding the packing coords EXTEND the claim point at the top).
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
            let e0 := mload(ex)
            let e1 := mload(add(ex, 32))
            let e2 := mload(add(ex, 64))
            let e3 := mload(add(ex, 96))
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
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_BASE_Z_COORDS) { i := add(i, 1) } {
                mstore(add(base, plen), shl(128, and(mload(add(POINT_PTR(), mul(i, 32))), MASK)))
                plen := add(plen, 16)
            }
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_PACK_LOG2) { i := add(i, 1) } {
                mstore(add(base, plen), shl(128, and(mload(add(ex, mul(32, i))), MASK)))
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
            mstore(4, commitment)
            mstore(36, pubval)
            mstore(68, setupval)
            pop(call(gas(), __TEMPLATE_REGISTRY_ADDRESS, 0, 0, 100, 0, 0))
        }

        // SPILL OVERWRITE PREVENTION
        if gt(mload(0x40), MINIMUM_FREE_HEAP_PTR) {
            revert(0, 0)
        }

        // INIT + MAIN. `alpha`, `init_gas`, `compress_gas` are confined to this block so
        // their stack slots free before the tail (assert/emit/return) — the legacy backend
        // does not spill, and keeping them live to the end runs the root `ptr` 1 slot too deep.
        // Gas deltas are stashed to heap (read back in the anti-DCE return), so scoping is safe.
        let ptr, claim, output_evals_ptr
        {
            let alpha
            mstore(GKR_INIT_GAS_PTR(), gas())
            mstore(SEED_PTR(), 0) // SEED Transcript, FINE as long as we don't draw without absorb!
            ptr := transcript_init(0)
            output_evals_ptr := ptr // base of the 10 GKR output columns (for the lookup-identity check)
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

        // Lookup identities: every logup argument's rational sum Σ num/den over the boundary
        // evaluations must be zero (same as the CPU verifier's lookup-identity check).
        check_lookup_identities(output_evals_ptr)

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
