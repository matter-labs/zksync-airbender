// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.38;

// Code-tail data. The generator (assemble.rs) builds this data for one circuit and setup, and
// GkrWhirVerifier's constructor returns GkrWhirVerifierCode.runtimeCode followed by it, so the
// data is part of the deployed code. In order:
//   - one STOP byte at the start of the data;
//   - the setup frontier: the setup commitment's Merkle nodes at __TEMPLATE_FRONTIER_LEVEL, in
//     physical order; setup query paths end at these nodes, and the generator checks that they
//     hash up to the setup cap (__TEMPLATE_DATA_FRONTIER_OFFSET);
//   - the setup cap in its transcript-preimage form, copied into the preimage before
//     transcript_init (__TEMPLATE_DATA_CAP_OFFSET, __TEMPLATE_DATA_CAP_BYTES);
//   - the layer-0 term table: packed quadratic and linear terms of max-quadratic gate relations
//     (gate slot, columns, coefficient), read by the bucket loops in sumcheck_circuit_layer0
//     (__TEMPLATE_DATA_QTABLE_OFFSET, __TEMPLATE_DATA_QTABLE_BYTES).
// The fallback computes the data's start as codesize() - __TEMPLATE_SETUP_DATA_BYTES and keeps it
// at SETUP_CODE_OFFSET_PTR. MEMORY_LAYOUT.md next to the generated verifier gives the byte ranges.

/// The registry every successfully verified statement is reported to (one call per proof).
interface IVerificationRegistry {
    /// `publicInput`     = final registers x10..x17 (a0..a7), each u32 LE, concatenated;
    /// `auxInput`        = final registers x18..x25 (s2..s9), same encoding: the recursion chain
    ///                     hash, which the verifier does not check — the registry must compare it
    ///                     with the expected chain of the program it accepts;
    /// The registry must accept only approved verifier addresses (`msg.sender`), each pinned
    /// to one setup embedded in its runtime code.
    function markVerified(bytes32 publicInput, bytes32 auxInput) external;
}

/// Runtime code used by GkrWhirVerifier's constructor, which appends the generated setup data.
contract GkrWhirVerifierCode {
    address constant __TEMPLATE_REGISTRY = address(0x0078d549f2a140923c517c23b008dffe979b3c4e91);

    // Every `__TEMPLATE_*` constant below is assigned by the generator (assemble.rs); in the
    // template they hold the string literal "{unassigned}", which does not compile as a number —
    // a generator that forgets one cannot produce a buildable verifier. Inline assembly can only
    // consume literal (numeric-expression) constants, so the literal lives in the declaration.

    uint256 constant __TEMPLATE_GKR_LAYER_0_CLAIMS = 74; // previous-layer output claims batched by sccl0
    uint256 constant __TEMPLATE_GKR_LAYER_1_CLAIMS = 26; // previous-layer output claims batched by sccl1
    uint256 constant __TEMPLATE_GKR_LAYER_2_CLAIMS = 18; // previous-layer output claims batched by sccl2
    uint256 constant __TEMPLATE_GKR_LAYER_3_CLAIMS = 12; // previous-layer output claims batched by sccl3
    uint256 constant __TEMPLATE_GKR_LAYER_4_CLAIMS = 10; // previous-layer output claims batched by sccl4

    // ── Generic (used throughout) ───────────────────────────────────────────
    uint256 constant MINIMUM_FREE_HEAP_PTR = 2048; // above via_ir's memoryguard reservation (guarded below)
    uint256 constant P      = 0x7000000000000000000000000000001; // Proth120: 7*2^120 + 1
    uint256 constant MASK   = 0xffffffffffffffffffffffffffffffff; // low 128 bits (one field lane)
    uint256 constant FE_BITS = 123; // bits per field element in a calldata FE run (P < 2^123)
    uint256 constant FE_MASK = 0x7ffffffffffffffffffffffffffffff; // 2^FE_BITS - 1
    // Stack-pressure fix: the ~123-bit modulus P as a literal is a PUSH16 rematerialized at
    // every addmod/mulmod, and the Yul scheduler keeps it live across the deep gate sequences
    // (→ "stack too deep"). Store P once at a heap offset and `mload(P_PTR)` it where stack depth
    // matters (the generated circuit gates and the GKR helpers); the fallback stores it first.
    //
    // MEMORY LAYOUT (matters under via_ir): solc's IR backend places its stack-spill slots at
    // fixed low offsets that grow up from 0x80, and the SPILL-OVERWRITE guard (before the GKR
    // half runs) asserts they never reach MINIMUM_FREE_HEAP_PTR. So the region
    // [0x80, MINIMUM_FREE_HEAP_PTR) is the spill zone and [MINIMUM_FREE_HEAP_PTR, ∞) is
    // spill-safe. P_PTR / CIRCUIT_PTR MUST live in the safe region — a low fixed slot is
    // silently clobbered by via_ir spills, corrupting the committed state. They take
    // the first two slots of the safe region; the setup code offset takes the third. The generated heap starts 96 bytes
    // higher. INVARIANT (Yul forbids constant arithmetic in assembly, so these are spelled as
    // literals): P_PTR == MINIMUM_FREE_HEAP_PTR, CIRCUIT_PTR == MINIMUM_FREE_HEAP_PTR + 32, and
    // the generator starts the heap at MINIMUM_FREE_HEAP_PTR + 96 (it reads the constant).
    uint256 constant P_PTR  = 2048;      // == MINIMUM_FREE_HEAP_PTR  (spill-safe slot 0)
    // Fixed heap slot holding the circuit-layer image cursor, so gate/cache sub-functions
    // read it via mload instead of a `ptr` parameter (that param was the single deepest stack
    // slot pushing each of them 1 over the EVM limit). Spill-safe slot 1, just above P_PTR.
    uint256 constant CIRCUIT_PTR = 2080; // == MINIMUM_FREE_HEAP_PTR + 32
    // Spill-safe slot [2112,2144): after P_PTR and CIRCUIT_PTR, before every generated
    // GKR/WHIR heap region (which starts at 2144). The generator checks these boundaries.
    // This is the address of the memory slot holding the setup data code offset, computed
    // at runtime from codesize(). It is unrelated to cap size or preimage length. Solidity
    // metadata precedes that data and cannot change this tail-relative offset.
    uint256 constant SETUP_CODE_OFFSET_PTR = 2112;

    // ── Heap layout (GENERATED sizes: the regions are chained back to back from
    //    MINIMUM_FREE_HEAP_PTR + 96 by the `*_PTR()` accessors below, each region's size — a
    //    whole number of 32-byte words — derived from the circuit / prover config, see
    //    gkr_heap_regions in assemble.rs). NOTE: the accessors are deliberately a chain of
    //    `add(previous(), SIZE)` calls rather than absolute literals — with absolute literals the
    //    IR optimizer emits markedly more bytecode for the layer-0 gates. The WHIR half's regions
    //    follow at the chain's
    //    end (its generated absolute offsets; the generator's allocator places the WHIR map
    //    right after the chain).
    // HEAP ORDER: memory challenges (7), logup challenges (2), point (rounds),
    // seed + transcript scratch (absorb scratch at SEED+32/+64, cache array, claims-batch absorbs),
    // batching (1), dim-reduce claims (NUM_OUTPUTS), eq (max(OUTPUT_EVALS, NUM_OUTPUTS)),
    // absorb scratch (32 + max absorb), circuit claims (widest layer),
    // layer-0 gate values (gate slots), layer-0 packed term table, decoded calldata image.
    uint256 constant __TEMPLATE_GKR_MEMORY_CHALLS_BYTES  = 32 * 7;
    uint256 constant __TEMPLATE_GKR_LOGUP_CHALLS_BYTES   = 32 * 2;
    uint256 constant __TEMPLATE_GKR_POINT_BYTES          = 32 * 22;
    uint256 constant __TEMPLATE_GKR_CACHE_OFFSET         = 448; // after every seed-relative absorb
    uint256 constant __TEMPLATE_GKR_SEED_BYTES           = 32 * 34;
    uint256 constant __TEMPLATE_GKR_BATCHING_BYTES       = 32;
    uint256 constant __TEMPLATE_GKR_CLAIMS_BYTES         = 32 * 10;
    uint256 constant __TEMPLATE_GKR_EQ_BYTES             = 32 * 10;
    uint256 constant __TEMPLATE_GKR_ABS_BYTES            = 32 * 64;
    uint256 constant __TEMPLATE_GKR_CIRCUIT_CLAIMS_BYTES = 32 * 74;
    uint256 constant __TEMPLATE_GKR_GATEVAL_BYTES        = 32 * 120;
    uint256 constant __TEMPLATE_GKR_QTABLE_BYTES         = 32 * 105;

    // ── Transcript preimage: registers ‖ final_pc/ts ‖ inits/teardowns top_bits ‖ setup_cap ‖
    //    memory_cap (LE u32 words). The register prefix is the RISC-V machine state (fixed);
    //    the tail offsets depend on the circuit (teardown sets) and config (cap) → generated. ──
    uint256 constant NUM_REGISTERS              = 32;
    uint256 constant PREIMAGE_REGISTER_STRIDE   = 12; // (value, ts_low, ts_high) as LE u32
    uint256 constant PUBLIC_INPUT_FIRST_REGISTER = 10; // x10..x17 (a0..a7)
    uint256 constant AUX_INPUT_FIRST_REGISTER    = 18; // x18..x25 (s2..s9)
    uint256 constant MARK_WORD_REGISTERS         = 8;  // 8 u32 values = one bytes32
    uint256 constant __TEMPLATE_PREIMAGE_FINAL_PC_OFFSET       = 32 * 12; // NUM_REGISTERS * PREIMAGE_REGISTER_STRIDE
    uint256 constant __TEMPLATE_PREIMAGE_TIMESTAMP_LOW_OFFSET  = 32 * 12 + 4;
    uint256 constant __TEMPLATE_PREIMAGE_TIMESTAMP_HIGH_OFFSET = 32 * 12 + 8;
    uint256 constant __TEMPLATE_PREIMAGE_TOP_BITS_OFFSET       = 32 * 12 + 12;
    uint256 constant __TEMPLATE_PREIMAGE_TOP_BITS_BYTES        = 4 * 2;
    uint256 constant __TEMPLATE_PREIMAGE_SETUP_CAP_OFFSET      = 32 * 12 + 12 + 4 * 2;
    uint256 constant __TEMPLATE_PREIMAGE_MEMORY_CAP_OFFSET     = 32 * 12 + 12 + 4 * 2 + 32 * 8 * 4;
    uint256 constant __TEMPLATE_PREIMAGE_CAP_BYTES             = 32 * 8 * 4;
    uint256 constant __TEMPLATE_GKR_INIT_PREIMAGE_BYTES    = 32 * 12 + 12 + 4 * 2 + 32 * 8 * 4 + 32 * 8 * 4; // registers ‖ final PC ‖ top bits ‖ setup cap ‖ memory cap
    uint256 constant __TEMPLATE_FACTORED_ROUND_SLOT_BYTES = 32; // image bytes of a factored-round run: its calldata bit offset
    // The inits/teardowns RAM-set base chunk indices (`top_bits`) are deployment parameters of
    // the program: decode_calldata writes them into the preimage, and the layer-0
    // inits/teardowns gates use the constants. One uint8 per teardown set.
    uint8 constant __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_0 = 0;
    uint8 constant __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_1 = 1;
    uint256 constant __TEMPLATE_EXTERNAL_POW_BITS = 20; // external-challenge PoW difficulty

    // ── GKR entry + dimension reduction (generated from the circuit / config) ─────────────────
    uint256 constant __TEMPLATE_GKR_NUM_OUTPUTS        = 5 * 2; // GKR output polys (global_output_map lines)
    // Logical output columns, generated by flattening global_output_map in OutputType order.
    uint256 constant __TEMPLATE_GKR_OUTPUT_PERM_READ = 0;
    uint256 constant __TEMPLATE_GKR_OUTPUT_PERM_WRITE = 1;
    uint256 constant __TEMPLATE_GKR_OUTPUT_LOOKUP16_NUM = 2;
    uint256 constant __TEMPLATE_GKR_OUTPUT_LOOKUP16_DEN = 3;
    uint256 constant __TEMPLATE_GKR_OUTPUT_LOOKUP_TS_NUM = 4;
    uint256 constant __TEMPLATE_GKR_OUTPUT_LOOKUP_TS_DEN = 5;
    uint256 constant __TEMPLATE_GKR_OUTPUT_GENERIC_LOOKUP_NUM = 6;
    uint256 constant __TEMPLATE_GKR_OUTPUT_GENERIC_LOOKUP_DEN = 7;
    uint256 constant __TEMPLATE_GKR_OUTPUT_TEARDOWN = 8;
    uint256 constant __TEMPLATE_GKR_OUTPUT_INIT = 9;
    uint256 constant __TEMPLATE_GKR_OUTPUT_LOG2        = 2; // log2 of the explicit output layer (sumcheck_explicit_output_size_log_2)
    uint256 constant __TEMPLATE_GKR_OUTPUT_EVALS       = 1 << 2; // 2^OUTPUT_LOG2 evals per output poly
    uint256 constant __TEMPLATE_GKR_INIT_BYTES         = 10 * 4 * 16; // NUM_OUTPUTS * OUTPUT_EVALS * 16 (one u128 per eval)
    uint256 constant __TEMPLATE_GKR_LSB_LINES_BYTES    = 10 * 32; // NUM_OUTPUTS * 32 (one [E;2] line per output)
    uint256 constant __TEMPLATE_GKR_DIM_REDUCE_LAYERS  = 22 - 2; // trace_log2 - OUTPUT_LOG2
    uint256 constant __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS = 22; // trace_log2

    // ── GKR→WHIR handoff (generated; shared with the WHIR half where the names coincide) ──────
    uint256 constant __TEMPLATE_WHIR_CAP            = 1 << 5; // base-oracle merkle cap size
    uint256 constant __TEMPLATE_WHIR_BATCH_POW_BITS = 32; // batched_proximity_check_pow_bits
    // Base-layer at-point claims (dense in layer 0's eval block of the image): mem++wit = NUM_MEMWIT
    // cols, setup = NUM_SETUP cols. The merge folds each 2^PACK_LOG2-chunk by the PACK_LOG2
    // packing coords: NUM_MEMWIT -> MERGED_MW claims, NUM_SETUP -> SETUP_MERGED claims.
    uint256 constant __TEMPLATE_WHIR_PACK_LOG2      = 3;
    uint256 constant __TEMPLATE_WHIR_PACK           = 1 << 3; // 2^PACK_LOG2
    uint256 constant __TEMPLATE_WHIR_NUM_MEMWIT     = 38 + 58; // memory_layout + witness_layout total widths
    uint256 constant __TEMPLATE_WHIR_NUM_SETUP      = 10; // generic_lookup_tables_width
    uint256 constant __TEMPLATE_WHIR_MERGED_MW      = (96 + 8 - 1) >> 3; // ceil(NUM_MEMWIT / PACK)
    uint256 constant __TEMPLATE_WHIR_SETUP_MERGED   = (10 + 8 - 1) >> 3; // ceil(NUM_SETUP / PACK)
    // emit_gkr_mark's ABS-region scratch: packing coords at +0, merged claims at MERGED_OFFSET,
    // whir_fold_pack's PACK-slot chunk buffer at FOLD_OFFSET (generated, disjoint).
    uint256 constant __TEMPLATE_GKR_HANDOFF_MERGED_OFFSET = 32 * 3; // 32 * PACK_LOG2
    uint256 constant __TEMPLATE_GKR_HANDOFF_FOLD_OFFSET   = 32 * 17; // MERGED_OFFSET + 32 * (MERGED_MW + SETUP_MERGED)
    uint256 constant __TEMPLATE_WHIR_BASE_Z_COORDS  = 22; // layer-0 folding point length (= trace_log2)
    // The WHIR half's own constants (schedule + memory map) are spliced in here:
    uint256 constant W_HALF = 0x3800000000000000000000000000001;  // 2^-1 = (P+1)/2

    // ── Generated from the prover config + circuit (`__TEMPLATE_WHIR_*`) ─────────────────────
    // Every value below is assigned by the generator (see the note on `__TEMPLATE_*` constants in
    // the GKR template).
    // RS-codeword evaluation-domain generator and its inverse — a primitive 2^base_domain_log2-th
    // root of unity (`Proth120::TWO_ADICITY_GENERATORS[base_domain_log2]`).
    uint256 constant __TEMPLATE_WHIR_BASE_DOMAIN_ROOT     = 0x048B6B79BA191BD30B0910E6758FBC8E;
    uint256 constant __TEMPLATE_WHIR_BASE_DOMAIN_ROOT_INV = 0x0521CD7F2760EB0D44309DC8A890B5C2;
    uint256 constant __TEMPLATE_WHIR_NUM_ROUNDS   = 6;
    uint256 constant __TEMPLATE_WHIR_RFIN         = 25 - (1 + 1 + 4 + 4 + 4 + 4);  // final-poly log2 = message_log2 - sum(folds)
    // Merkle cap: each commitment is a cap of 2^CAP_LOG2 hashes, so a Merkle path is CAP_LOG2
    // levels shorter. Caps shrink paths but grow every commitment to CAP*32 bytes.
    uint256 constant __TEMPLATE_WHIR_CAP_LOG2 = 5;
    // Merkle leaf/node hash: keccak256 truncated to the digest bytes (the high bytes kept).
    uint256 constant __TEMPLATE_DIGEST_MASK = 0xffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000;
    uint256 constant __TEMPLATE_DIGEST_BYTES = 25; // Merkle digest bytes in the compressed calldata
    // Appended setup data: STOP ‖ setup frontier ‖ pinned setup cap image ‖ GKR term table.
    // It ends at codesize(); all setup offsets are relative to its leading STOP.
    uint256 constant __TEMPLATE_SETUP_DATA_BYTES = 29978;
    uint256 constant __TEMPLATE_DATA_FRONTIER_OFFSET = 1;
    uint256 constant __TEMPLATE_DATA_CAP_BYTES = 1024;
    uint256 constant __TEMPLATE_DATA_QTABLE_BYTES = 3353;
    uint256 constant __TEMPLATE_DATA_CAP_OFFSET = 25601;
    uint256 constant __TEMPLATE_DATA_QTABLE_OFFSET = 26625;
    // Setup frontier: the setup tree's 2^LEVEL nodes at that level (DIGEST_BYTES each, physical
    // order) after the STOP byte; setup paths stop SKIP = LEVEL − CAP_LOG2 levels early.
    uint256 constant __TEMPLATE_FRONTIER_LEVEL = 10;
    uint256 constant __TEMPLATE_FRONTIER_SKIP = 5;

    // ── Memory map (generated: contiguous regions above the GKR heap, each sized from the
    //    schedule — see WhirGenConfig::memory_regions for every region's size formula) ────────
    uint256 constant __TEMPLATE_WHIR_SEED_PTR     = 30624;  // seed + in-place absorb scratch
    uint256 constant __TEMPLATE_WHIR_Z_PTR        = 31680;  // z: the evaluation-point coords
    uint256 constant __TEMPLATE_WHIR_POW_PTR      = 32480;  // (scalar, running eq, coefficient) x numpow
    uint256 constant __TEMPLATE_WHIR_ACC_PREF_PTR = 41120;
    uint256 constant __TEMPLATE_WHIR_GAMMA_PTR    = 41152;  // one gamma power per batched base column
    uint256 constant __TEMPLATE_WHIR_FOLD_CH_PTR  = 41600;  // max_fold challenges
    uint256 constant __TEMPLATE_WHIR_HPO_PTR      = 41728;  // 2^(fold_0 - 1) high-power offsets (round 0)
    uint256 constant __TEMPLATE_WHIR_FBUF_PTR     = 41760;  // 2^max_fold folding buffer
    uint256 constant __TEMPLATE_WHIR_LEAF_PTR     = 42272;  // leaf hashing scratch
    uint256 constant __TEMPLATE_WHIR_REG_CD       = 42656;  // calldata cursor
    uint256 constant __TEMPLATE_WHIR_REG_CLAIM    = 42688;
    uint256 constant __TEMPLATE_WHIR_REG_NUMPOW   = 42720;
    uint256 constant __TEMPLATE_WHIR_REG_ZIOFF    = 42752;
    uint256 constant __TEMPLATE_WHIR_REG_CC       = 42784;
    uint256 constant __TEMPLATE_WHIR_REG_CURDELIN = 42816;
    // cap regions (CAP*32 bytes each)
    uint256 constant __TEMPLATE_WHIR_BCAP0_PTR    = 42848;  // memory+witness base-oracle cap
    uint256 constant __TEMPLATE_WHIR_QCAP_PTR     = 43872;  // current query cap (rounds >= 1)
    uint256 constant __TEMPLATE_WHIR_NCAP_PTR     = 44896;  // just-read intermediate cap
    // Per-round query drawing (matches prover `draw_query_bits`/`BitSource`):
    //   QIDX_BUF holds the drawn query indices (max_q words);
    //   DRAW_BUF holds the little-endian u32 words squeezed from the seed (one per slot).
    uint256 constant __TEMPLATE_WHIR_QIDX_BUF_PTR = 45920;
    uint256 constant __TEMPLATE_WHIR_DRAW_BUF_PTR = 46624;
    // do_final scratch: the plain-text tail is 2^RFIN monomials (MONO), then the tail absorb +
    // halving-fold scratch (FEVAL, 2^RFIN words).
    uint256 constant __TEMPLATE_WHIR_MONO_PTR     = 47392;
    uint256 constant __TEMPLATE_WHIR_FEVAL_PTR    = 51488;

    fallback(bytes calldata) external returns (bytes memory) {
        // The verified statement, assembled from the preimage inside the assembly block (mark_word)
        // and reported through the typed registry interface below (the compiler does the ABI
        // encoding of both the call and the return data).
        bytes32 publicInput;
        bytes32 auxInput;
        // "memory-safe" lets solc spill stack slots, which the deepest functions need (without it
        // check_permutation_identity is too deep for the stack). The hand-placed heap starts above
        // the spill zone (MEMORY LAYOUT above).
        assembly ("memory-safe") {
        mstore(P_PTR, 0x7000000000000000000000000000001)
        mstore(SETUP_CODE_OFFSET_PTR, sub(codesize(), __TEMPLATE_SETUP_DATA_BYTES))
        // decode_calldata (below) unpacks the compressed calldata into the decoded GKR image the
        // GKR half reads, in transcript order. The image holds field elements as BE 16-byte
        // lanes, two per word: x0 = shr(128, word), x1 = and(word, MASK). Challenges take the
        // high 16 hash bytes: mod(shr(128, seed), P).

        // Heap regions, chained by their GENERATED sizes (the generated circuit.yul calls these
        // by name). The chain order here is verified by the generator against its allocator.
        // 96 skips three reserved 32-byte slots: P_PTR, CIRCUIT_PTR, SETUP_CODE_OFFSET_PTR.
        function MEMORY_CHALLS_PTR() -> ptr { ptr := add(MINIMUM_FREE_HEAP_PTR, 96) }
        function LOGUP_CHALLS_PTR()  -> ptr { ptr := add(MEMORY_CHALLS_PTR(), __TEMPLATE_GKR_MEMORY_CHALLS_BYTES) }
        function POINT_PTR()         -> ptr { ptr := add(LOGUP_CHALLS_PTR(), __TEMPLATE_GKR_LOGUP_CHALLS_BYTES) }
        // The seed region also holds the transcript scratch the absorbs use at SEED+32/+64, the
        // per-layer cache array (circuit.yul) and the claims sumcheck_claims_batch absorbs at
        // SEED+32. Caches start after every absorb; the generator sizes both disjoint areas.
        function SEED_PTR()          -> ptr { ptr := add(POINT_PTR(), __TEMPLATE_GKR_POINT_BYTES) }
        function GKR_CIRCUIT_CACHE_PTR()  -> ptr { ptr := add(SEED_PTR(), __TEMPLATE_GKR_CACHE_OFFSET) }
        // Dim-reducing / entry regions (used before the circuit layers).
        function GKR_BATCHING_PTR() -> ptr { ptr := add(SEED_PTR(), __TEMPLATE_GKR_SEED_BYTES) }                 // running batching
        function GKR_CLAIMS_PTR()   -> ptr { ptr := add(GKR_BATCHING_PTR(), __TEMPLATE_GKR_BATCHING_BYTES) }     // NUM_OUTPUTS dim-reduce claims
        function GKR_EQ_PTR()       -> ptr { ptr := add(GKR_CLAIMS_PTR(), __TEMPLATE_GKR_CLAIMS_BYTES) }         // eq[OUTPUT_EVALS] / SI[NUM_OUTPUTS]
        function GKR_ABS_PTR()      -> ptr { ptr := add(GKR_EQ_PTR(), __TEMPLATE_GKR_EQ_BYTES) }                 // absorb scratch (32 + max absorb)
        // Circuit-layer claims array: the previous circuit layer's at-point evals,
        // offset-indexed, that this layer's `compute_claim` batches into its initial claim.
        // Threaded across layers: each layer writes its input evals here for the next one.
        // Sized by the generator for the widest layer.
        function GKR_CIRCUIT_CLAIMS_PTR() -> ptr { ptr := add(GKR_ABS_PTR(), __TEMPLATE_GKR_ABS_BYTES) }

        // Layer-0 table-driven quadratic-gate evaluation. emit_layer0_quad_table seeds GATEVAL
        // with Proth120::to_u128 constants and updates it with addmod, so each value is reduced.
        // Horner chunks read these values as mload(GATEVAL + 32*slot). QTABLE holds packed
        // records (slot, a, b, coeff) copied from the embedded setup. GATEVAL is not written
        // before layer 0, so it needs no zeroing; only layer 0's point-check uses these regions.
        function GKR_GATEVAL_PTR() -> ptr { ptr := add(GKR_CIRCUIT_CLAIMS_PTR(), __TEMPLATE_GKR_CIRCUIT_CLAIMS_BYTES) }
        function GKR_QTABLE_PTR()  -> ptr { ptr := add(GKR_GATEVAL_PTR(), __TEMPLATE_GKR_GATEVAL_BYTES) }
        // The decoded GKR image, written once by decode_calldata; the verifier reads it at image
        // offsets.
        function IMAGE_PTR()       -> ptr { ptr := add(GKR_QTABLE_PTR(), __TEMPLATE_GKR_QTABLE_BYTES) }

        // ── Calldata decoder: the GKR half's only calldata reader. Writes the decoded GKR image
        // at IMAGE_PTR(); the GKR half reads that image at image offsets, the WHIR half reads its
        // stream from calldata after the GKR section.
        // FE-run(n) at cd: element j = bits [123j, 123j + 123) MSB-first, the pad bits of the last
        // byte zero. Elements 2i, 2i + 1 lie in the word loaded at byte bit >> 3 (bit & 7 ≤ 7,
        // 7 + 246 ≤ 256) and go to the two u128 lanes at dst + 32i. No range check here: the
        // gkr_init checks output lanes, gkr_dr_final checks LSB lines, and
        // The following functions check at-point lanes < P:
        // sumcheck_circuit_layer0, sumcheck_circuit_layer1
        // sumcheck_circuit_layer2, sumcheck_circuit_layer3
        // sumcheck_circuit_layer4
        function fe_pair_lanes(x) -> w {
            w := or(shl(128, and(shr(FE_BITS, x), FE_MASK)), and(x, FE_MASK))
        }
        function decode_run(cd, n, dst) {
            // Four pairs = 984 bits = 123 bytes (8 fields); shr(3,n) counts 8-field blocks.
            // Pair k starts at byte floor(246*k/8): 0/30/61/92; align by 10-(246*k & 7): 10/4/6/8.
            // Destination offsets 0/32/64/96 hold four packed pairs; advance by 128 bytes.
            for { let end := add(cd, mul(123, shr(3, n))) } lt(cd, end) { cd := add(cd, 123) } {
                mstore(dst, fe_pair_lanes(shr(10, calldataload(cd))))
                mstore(add(dst, 32), fe_pair_lanes(shr(4, calldataload(add(cd, 30)))))
                mstore(add(dst, 64), fe_pair_lanes(shr(6, calldataload(add(cd, 61)))))
                mstore(add(dst, 96), fe_pair_lanes(shr(8, calldataload(add(cd, 92)))))
                dst := add(dst, 128)
            }
            // Remainder: (n/2)&3 pairs after the 8-field blocks; shift 1 divides by 2,
            // mask 3 takes modulo 4, and each packed pair occupies 246 bits.
            let bit := 0
            for { let end := mul(246, and(shr(1, n), 3)) } lt(bit, end) { bit := add(bit, 246) } {
                mstore(dst, fe_pair_lanes(shr(sub(10, and(bit, 7)), calldataload(add(cd, shr(3, bit))))))
                dst := add(dst, 32)
            }
            check_run_pad(cd, bit)
        }
        // The pad bits after `bits` run bits at cd must be zero. Mask 7 computes pad modulo 8;
        // (bits+pad-1)>>3 locates the final byte, and (1<<pad)-1 selects its unused low bits.
        function check_run_pad(cd, bits) {
            let pad := and(sub(0, bits), 7)
            if and(byte(0, calldataload(add(cd, shr(3, sub(add(bits, pad), 1))))), sub(shl(pad, 1), 1)) { revert(0, 0) }
        }
        // decode_run over the run at (cd, image): the next calldata and image offsets.
        // (bits+7)>>3 rounds to bytes; shl(4,n) allocates n * 16-byte u128 lanes.
        function decode_next_run(cd, image, n) -> next_cd, next_image {
            decode_run(cd, n, add(IMAGE_PTR(), image))
            next_cd := add(cd, shr(3, add(mul(FE_BITS, n), 7)))
            next_image := add(image, shl(4, n))
        }
        // Factored-round run of k (b, c) pairs: the round functions read the pairs from calldata
        // (cd_load); factored_round checks both < P. The image slot holds cd * 8 (shl(3, cd));
        // shl(1, k) counts two fields per round. The
        // decoder shares run_end and cd_digest with the WHIR half (whir.sol).
        function record_factored_run(cd, image, k) -> next_cd, next_image {
            mstore(add(IMAGE_PTR(), image), shl(3, cd))
            next_cd := run_end(cd, shl(1, k))
            next_image := add(image, 32)
        }
        function cd_load(off) -> w {
            w := calldataload(off)
        }
        // A 19-bit limb as 4 LE u32 bytes, left-aligned: byte shifts 248/240/232 = 256-8/16/24;
        // 0xff selects one byte, and shifts 8/16 select the next source bytes.
        function limb19_le(x) -> w {
            w := or(or(shl(248, and(x, 0xff)), shl(240, and(shr(8, x), 0xff))), shl(232, shr(16, x)))
        }
        // TS-run pair i: bits [38i, 38i + 38) = low19 | high19; 218 = 256-38.
        // Masks 0x3fffffffff/0x7ffff select 38/19 bits; bit&7 and bit>>3 address a byte.
        function cd_timestamp(i) -> lo, hi {
            let bit := mul(38, i)
            let x := and(shr(sub(218, and(bit, 7)), calldataload(add(128, shr(3, bit)))), 0x3fffffffff)
            lo := shr(19, x)
            hi := and(x, 0x7ffff)
        }
        // Byte-reverse each u32 lane of a 32-byte word (BE digest words to preimage LE words):
        // alternating ff00/00ff masks swap bytes via shifts 8, then ffff0000/0000ffff swap
        // 16-bit halves via shifts 16, independently within each 4-byte lane.
        function bswap32x8(w) -> r {
            r := or(shr(8, and(w, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00)),
                    shl(8, and(w, 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff)))
            r := or(shr(16, and(r, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000)),
                    shl(16, and(r, 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff)))
        }
        function decode_calldata() {
            // Build the transcript preimage hashed by transcript_init, field by field.
            // Registers (value, ts_low, ts_high) are 4-byte LE u32s at byte offsets 0/4/8.
            // shl(224, pc) left-aligns its 32 bits (256-32=224); setup cap comes from code.
            for { let i := 0 } lt(i, NUM_REGISTERS) { i := add(i, 1) } {
                let dst := add(IMAGE_PTR(), mul(PREIMAGE_REGISTER_STRIDE, i))
                calldatacopy(dst, mul(4, i), 4)
                let lo, hi := cd_timestamp(i)
                mstore(add(dst, 4), limb19_le(lo))
                mstore(add(dst, 8), limb19_le(hi))
            }
            {
                let lo, hi := cd_timestamp(NUM_REGISTERS)
                mstore(add(IMAGE_PTR(), __TEMPLATE_PREIMAGE_FINAL_PC_OFFSET), shl(224, 0x74320400)) // pinned final PC
                mstore(add(IMAGE_PTR(), __TEMPLATE_PREIMAGE_TIMESTAMP_LOW_OFFSET), limb19_le(lo))
                mstore(add(IMAGE_PTR(), __TEMPLATE_PREIMAGE_TIMESTAMP_HIGH_OFFSET), limb19_le(hi))
            }
            // Timestamp pad mask 0x3 selects the final 2 unused low bits.
            if and(byte(0, calldataload(284)), 0x3) { revert(0, 0) }
            // pinned inits/teardowns top bits (the setup cap below overwrites the rest of the word)
            mstore(add(IMAGE_PTR(), __TEMPLATE_PREIMAGE_TOP_BITS_OFFSET), 0x0000000001000000000000000000000000000000000000000000000000000000)
            // pinned setup cap
            codecopy(add(IMAGE_PTR(), __TEMPLATE_PREIMAGE_SETUP_CAP_OFFSET), add(mload(SETUP_CODE_OFFSET_PTR), __TEMPLATE_DATA_CAP_OFFSET), __TEMPLATE_DATA_CAP_BYTES)
            // memory cap at calldata byte 285: 32 digests of 25 bytes, as preimage LE words and as the WHIR
            // half's BE base-oracle cap
            for { let i := 0 } lt(i, 32) { i := add(i, 1) } {
                let d := cd_digest(add(285, mul(25, i)))
                mstore(add(IMAGE_PTR(), add(__TEMPLATE_PREIMAGE_MEMORY_CAP_OFFSET, mul(32, i))), bswap32x8(d))
                mstore(add(__TEMPLATE_WHIR_BCAP0_PTR, mul(32, i)), d)
            }
            // Wire preimage: 1085 bytes = register u32s + packed timestamps + wire cap.
            // Decode 40 output-evaluation lanes, then layers with k=2..22 sumcheck rounds.
            // Each dimension-reduction boundary has 20 lanes (two per output polynomial).
            let cd := 1085
            let image := __TEMPLATE_GKR_INIT_PREIMAGE_BYTES
            calldatacopy(add(IMAGE_PTR(), image), cd, 8) // external PoW nonce
            cd, image := decode_next_run(add(cd, 8), add(image, 8), 40)
            for { let k := 2 } lt(k, 22) { k := add(k, 1) } {
                cd, image := record_factored_run(cd, image, k)
                cd, image := decode_next_run(cd, image, 20)
            }
            // 5 circuit layers, top first; each at-point count is a 16-bit descriptor.
            // widths_word stores layer l in bits 16*l..16*l+16; 0xffff selects that count.
            for { let l := 0 } lt(l, 5) { l := add(l, 1) } {
                cd, image := record_factored_run(cd, image, 22)
                cd, image := decode_next_run(cd, image, and(shr(mul(16, l), 0x006a004a001a0012000c), 0xffff))
            }
            calldatacopy(add(IMAGE_PTR(), image), cd, 8) // WHIR batching PoW nonce
            // Include the trailing 8-byte nonce: calldata ends at 21971, image at 14084.
            if iszero(and(eq(add(cd, 8), 21971), eq(add(image, 8), 14084))) { revert(0, 0) }
        }

        // Read one little-endian u32 from the transcript preimage (byte offset in the image).
        // LE u32: byte indices 0..3 have shifts 0, 8, 16, 24 bits (8 bits per byte).
        function preimage_u32(byteoff) -> v {
            let w := mload(add(IMAGE_PTR(), byteoff))
            v := add(add(byte(0, w), shl(8, byte(1, w))), add(shl(16, byte(2, w)), shl(24, byte(3, w))))
        }

        // Seed (32 bytes) plus four u128 coefficients (64 bytes) totals 96; w1 starts at 64.
        // A 128-bit shift selects a packed u128 lane; mod below reduces the drawn challenge.
        function transcript_4to1_dual(w0, w1, modulus) -> r {
            // Absorb the four coefficients before drawing the round challenge:
            // seed = keccak(seed || w0 || w1), then seed = keccak(seed), r = top128 mod P.
            // w0 = [c0|c1], w1 = [c2|c3], each lane canonical via factored_round's addmod/mulmod outputs.
            mstore(add(SEED_PTR(), 32), w0)
            mstore(add(SEED_PTR(), 64), w1)
            let seed := keccak256(SEED_PTR(), 96) // absorb factored_round's 4 reduced coefficients
            mstore(SEED_PTR(), seed)
            seed := keccak256(SEED_PTR(), 32)     // draw
            mstore(SEED_PTR(), seed)
            r := mod(shr(128, seed), modulus)
        }

        // PoW hashes seed32 || nonce8 (40 bytes); 256 is the digest bit width.
        // Memory challenge slots 0..6 use byte offsets 0,32,64,96,128,160,192; logup slots 0..1 follow.
        // Each mod(shr(128, seed), P) below produces one canonical u128 challenge.
        function transcript_init(ptr) -> next_ptr {
            // SingleChunk commits the register/PC boundary, top bits and both caps.
            // Hash the LE-u32 preimage, absorb the BE-u64 nonce, check its configured PoW,
            // then draw permutation and lookup challenges.
            let seed := keccak256(ptr, __TEMPLATE_GKR_INIT_PREIMAGE_BYTES)

            // PoW fold: digest = keccak(seed(32) || nonce_be8); require top __TEMPLATE_EXTERNAL_POW_BITS zero.
            // the 40-byte hash covers the seed and the word's leading 8-byte BE nonce; the rest of the
            // word stays behind, and every later absorb writes the bytes it hashes
            mstore(SEED_PTR(), seed)
            mstore(add(SEED_PTR(), 32), mload(add(ptr, __TEMPLATE_GKR_INIT_PREIMAGE_BYTES)))
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

            // SEED_PTR now holds the post-transcript-init seed; the GKR entry (gkr_init) absorbs output evals next.
            next_ptr := add(ptr, add(__TEMPLATE_GKR_INIT_PREIMAGE_BYTES, 8)) // preimage + 8-byte PoW nonce
        }



        // Absorb the explicit output evaluations and draw the evaluation point plus
        // batching challenge. Build the OUTPUT_EVALS-entry equality table once and reuse it for
        // the NUM_OUTPUTS claims.
        // gkr_compress reads the claims and the batching from GKR_CLAIMS_PTR / GKR_BATCHING_PTR.
        // Packed field lanes use the high 128 bits. gkr_init reduces each drawn coordinate with mod.
        function gkr_init(ptr) -> next_ptr {
            let sp := SEED_PTR()
            // Absorb seed || output evaluations. The bulk copy keeps the original lanes;
            // gkr_init's claims loop below rejects val >= P before returning. Thus an accepted
            // proof's transcript contains canonical values without another read of the lanes.
            mstore(GKR_ABS_PTR(), mload(sp))
            mcopy(add(GKR_ABS_PTR(), 32), ptr, __TEMPLATE_GKR_INIT_BYTES)
            let seed := keccak256(GKR_ABS_PTR(), add(32, __TEMPLATE_GKR_INIT_BYTES))
            mstore(sp, seed)
            // draw eval_point[OUTPUT_LOG2] -> POINT_PTR, then batching -> GKR_BATCHING_PTR
            for { let i := 0 } lt(i, __TEMPLATE_GKR_OUTPUT_LOG2) { i := add(i, 1) } {
                seed := keccak256(sp, 32)
                mstore(sp, seed)
                mstore(add(POINT_PTR(), mul(i, 32)), mod(shr(128, seed), mload(P_PTR)))
            }
            seed := keccak256(sp, 32)
            mstore(sp, seed)
            mstore(GKR_BATCHING_PTR(), mod(shr(128, seed), mload(P_PTR)))

            // eq[OUTPUT_EVALS] over eval_point[OUTPUT_LOG2] (LSB binding: eq[j] = Π_v (bit_v(j)?
            // z[v] : 1-z[v]), index bit v pairs with point coordinate v — matches the prover's
            // make_eq_table_lsb_first over the drawn point)
            for { let j := 0 } lt(j, __TEMPLATE_GKR_OUTPUT_EVALS) { j := add(j, 1) } {
                let e := 1
                for { let v := 0 } lt(v, __TEMPLATE_GKR_OUTPUT_LOG2) { v := add(v, 1) } {
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
            // NUM_OUTPUTS claims: claim_c = Σ_j outputEval[c*OUTPUT_EVALS+j] * eq[j] (column c).
            for { let c := 0 } lt(c, __TEMPLATE_GKR_NUM_OUTPUTS) { c := add(c, 1) } {
                let acc := 0
                for { let j := 0 } lt(j, __TEMPLATE_GKR_OUTPUT_EVALS) { j := add(j, 1) } {
                    let k := add(mul(c, __TEMPLATE_GKR_OUTPUT_EVALS), j)
                    let val := shr(128, mload(add(ptr, mul(k, 16))))
                    // reject a non-canonical lane so the bulk-absorbed output evals bind to
                    // reduced values: gkr_init checks val < P here before returning
                    if iszero(lt(val, mload(P_PTR))) { revert(0, 0) }
                    acc := add(mulmod(val, mload(add(GKR_EQ_PTR(), mul(j, 32))), mload(P_PTR)), acc)
                }
                // only mulmod consumes the claims, so this mod is redundant; removing it saves nothing
                mstore(add(GKR_CLAIMS_PTR(), mul(c, 32)), mod(acc, mload(P_PTR)))
            }
            next_ptr := add(ptr, __TEMPLATE_GKR_INIT_BYTES)
        }

        // Permutation identity check (no inversions). The prover's grand-product self-check is
        //   (write_poly/read_poly)*(init_poly/teardown_poly)*(machine_write/machine_read) == 1.
        // Multiplying out gives the inverse-free equality the EVM verifier enforces instead:
        //   read_poly * teardown_poly * read_bnd  ==  write_poly * init_poly * write_bnd
        // where read_bnd/write_bnd are the register + PC boundary contributions built from the
        // register final state and PC in the transcript preimage.
        // Challenge/addr-space/index constants:
        //   perm-lin challenges mc[0..5]: ADDR_LOW=0, ADDR_HIGH=1, TS_LOW=2, TS_HIGH=3,
        //   VALUE_LOW=4, VALUE_HIGH=5; additive = mc@192. PC modeled as memory cell:
        //   PC_LOW=VALUE_LOW=4, PC_HIGH=VALUE_HIGH=5, PC_TS_LOW=2, PC_TS_HIGH=3.
        //   AddressSpaceType: Register=0, PC=2. INITIAL_PC=0, split(INITIAL_TIMESTAMP=4)=(4,0).
        // The polys are products of the output evals at `op` (gkr_init range-checked every lane), in
        // BTreeMap<OutputType> order: __TEMPLATE_GKR_OUTPUT_PERM_READ / _PERM_WRITE and
        // __TEMPLATE_GKR_OUTPUT_TEARDOWN / _INIT (the generator asserts the OutputType layout).
        // Memory tuple challenge slots 0..5 weight address-low/high, timestamp-low/high and
        // value-low/high; slot 6 is additive (byte offsets 0,32,64,96,128,160,192). A preimage
        // u32 is 4 bytes, so timestamp limbs start at +4/+8. Values split at 16 bits (low mask
        // 0xffff). PC uses address-space tag 2.
        function check_permutation_identity(op) {
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
            for { let r := 0 } lt(r, NUM_REGISTERS) { r := add(r, 1) } {
                let base := mul(r, PREIMAGE_REGISTER_STRIDE)
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
                // decode_calldata writes this program's pinned terminal PC into the preimage, and
                // the transcript hashes it, so the verified statement is bound to that PC.
                let pcv := preimage_u32(__TEMPLATE_PREIMAGE_FINAL_PC_OFFSET)
                let ts_low := preimage_u32(add(__TEMPLATE_PREIMAGE_FINAL_PC_OFFSET, 4))
                let ts_high := preimage_u32(add(__TEMPLATE_PREIMAGE_FINAL_PC_OFFSET, 8))
                let c := addmod(2, additive, Pm)
                c := addmod(c, mulmod(mc4, and(pcv, 0xffff), Pm), Pm)
                c := addmod(c, mulmod(mc5, shr(16, pcv), Pm), Pm)
                c := addmod(c, mulmod(mc2, ts_low, Pm), Pm)
                c := addmod(c, mulmod(mc3, ts_high, Pm), Pm)
                read_bnd := mulmod(read_bnd, c, Pm)
            }
            // PC write: initial pc=0, initial ts=(4,0) => PC(2) + mc2*4 + additive
            write_bnd := mulmod(write_bnd, addmod(addmod(2, additive, Pm), mulmod(mc2, 4, Pm), Pm), Pm)

            // read_poly * teardown * read_bnd vs write_poly * init * write_bnd
            let read_side := read_bnd
            let write_side := write_bnd
            for { let j := 0 } lt(j, __TEMPLATE_GKR_OUTPUT_EVALS) { j := add(j, 1) } {
                let read_poly := shr(128, mload(add(op, mul(16, add(mul(__TEMPLATE_GKR_OUTPUT_PERM_READ, __TEMPLATE_GKR_OUTPUT_EVALS), j)))))
                let teardown := shr(128, mload(add(op, mul(16, add(mul(__TEMPLATE_GKR_OUTPUT_TEARDOWN, __TEMPLATE_GKR_OUTPUT_EVALS), j)))))
                let write_poly := shr(128, mload(add(op, mul(16, add(mul(__TEMPLATE_GKR_OUTPUT_PERM_WRITE, __TEMPLATE_GKR_OUTPUT_EVALS), j)))))
                let init := shr(128, mload(add(op, mul(16, add(mul(__TEMPLATE_GKR_OUTPUT_INIT, __TEMPLATE_GKR_OUTPUT_EVALS), j)))))
                read_side := mulmod(read_side, mulmod(read_poly, teardown, Pm), Pm)
                write_side := mulmod(write_side, mulmod(write_poly, init, Pm), Pm)
            }
            if iszero(eq(read_side, write_side)) {
            revert(0, 0) }
        }

        // Lookup identities — the logup analogue of the permutation-identity check, mirroring the
        // CPU verifier's `gkr_lookup_identity_failed` gate. The GKR output columns are laid out
        // in OutputType order (all names prefixed __TEMPLATE_GKR_OUTPUT_):
        //   PermutationProduct: PERM_READ, PERM_WRITE
        //   Lookup16Bits: LOOKUP16_NUM, LOOKUP16_DEN
        //   LookupTimestamps: LOOKUP_TS_NUM, LOOKUP_TS_DEN
        //   GenericLookup: GENERIC_LOOKUP_NUM, GENERIC_LOOKUP_DEN
        //   InitsAndTeardownsProduct: TEARDOWN, INIT
        // Each column has __TEMPLATE_GKR_OUTPUT_EVALS boundary evals (u128 hi-lane at
        // `op + (col*__TEMPLATE_GKR_OUTPUT_EVALS + j)*16`). Each lookup argument is a (numerator,
        // denominator) pair; its rational sum Σ_j num_j/den_j over the evals must be exactly zero. Accumulate the sum
        // as a single fraction — acc_num = acc_num·d + n·acc_den, acc_den = acc_den·d — and require
        // acc_num == 0 with acc_den ≠ 0 (a vanishing denominator would make the sum ill-defined).
        // `op` is the output evals' image address (the pointer gkr_init read the evals from).
        // Three lookup kinds (16-bit, timestamp, generic), each with two adjacent numerator/denominator columns.
        // A packed u128 lane is extracted with shr(128, word).
        function check_lookup_identities(op) {
            let modulus := mload(P_PTR)
            // Three consecutive (num, den) pairs, two columns each; the generator validates
            // their OutputType order and widths. Start at the named Lookup16Bits pair.
            for { let lk := 0 } lt(lk, 3) { lk := add(lk, 1) } {
                let num_base := add(op, mul(mul(add(__TEMPLATE_GKR_OUTPUT_LOOKUP16_NUM, mul(lk, 2)), __TEMPLATE_GKR_OUTPUT_EVALS), 16))
                let den_base := add(num_base, mul(mul(sub(__TEMPLATE_GKR_OUTPUT_LOOKUP16_DEN, __TEMPLATE_GKR_OUTPUT_LOOKUP16_NUM), __TEMPLATE_GKR_OUTPUT_EVALS), 16))
                let acc_num := 0
                let acc_den := 1
                for { let j := 0 } lt(j, __TEMPLATE_GKR_OUTPUT_EVALS) { j := add(j, 1) } {
                    let n := shr(128, mload(add(num_base, mul(j, 16))))
                    let d := shr(128, mload(add(den_base, mul(j, 16))))
                    acc_num := addmod(mulmod(acc_num, d, modulus), mulmod(n, acc_den, modulus), modulus)
                    acc_den := mulmod(acc_den, d, modulus)
                }
                // Σ num/den == 0 with a non-vanishing denominator.
                if acc_num { revert(0, 0) }
                if iszero(acc_den) { revert(0, 0) }
            }
        }

        // One factored round: read (b, c) from the calldata pair at `bit`, a = K − z(b + c).
        // e_z(X) = t + sX with t = 1 − z, s = 2z − 1; u(X) = a + bX + cX².
        // p(X) = e_z(X)·u(X) = c0 + c1X + c2X² + c3X³, where
        // c0 = t·a, c1 = t·b + s·a, c2 = t·c + s·b, c3 = s·c.
        // factored_round reduces the coefficients with addmod/mulmod and absorbs them as
        // [c0|c1], [c2|c3] (128-bit lanes). It then draws r and computes K := a + br + cr².
        // t, s and a may stay unreduced until consumed by addmod/mulmod.
        // Two 123-bit fields occupy 246 bits: shift by 256-246=10 minus the bit-in-byte offset.
        // Mask 7 and shift 3 split a bit offset into its low 3 bits and byte offset; shift 128
        // packs the u128 lanes.
        function factored_round(bit, z, k, modulus) -> r, next_k {
            let x := shr(sub(10, and(bit, 7)), cd_load(shr(3, bit)))
            let b := and(shr(FE_BITS, x), FE_MASK)
            let c := and(x, FE_MASK)
            if iszero(and(lt(b, modulus), lt(c, modulus))) { revert(0, 0) }
            let a := add(k, sub(modulus, mulmod(z, add(b, c), modulus)))
            let t := add(1, sub(modulus, z))
            let s := add(add(z, z), sub(modulus, 1))
            r := transcript_4to1_dual(
                or(shl(128, mulmod(t, a, modulus)), addmod(mulmod(t, b, modulus), mulmod(s, a, modulus), modulus)),
                or(shl(128, addmod(mulmod(t, c, modulus), mulmod(s, b, modulus), modulus)), mulmod(s, c, modulus)),
                modulus)
            next_k := addmod(a, mulmod(r, addmod(b, mulmod(r, c, modulus), modulus), modulus), modulus)
        }
        // Each (b,c) pair advances 2 * FE_BITS = 246 bits.
        function sumcheck_rounds(ptr, claim, total_rounds) -> next_ptr, next_claim {
            let modulus := mload(P_PTR)
            // Factored rounds: u(X) = a + bX + cX², e_z(X) = t + sX, t = 1 − z, s = 2z − 1.
            // p(X) = e_z(X)·u(X) = c0 + c1X + c2X² + c3X³ with c0 = t·a, c1 = t·b + s·a,
            // c2 = t·c + s·b, c3 = s·c; factored_round's addmod/mulmod reduce each absorbed 128-bit lane.
            // claim tracks K = u_prev(r_prev); a = K − z(b + c) makes p(0) + p(1) = K, so the
            // layer's end check is g == K. The (b, c) pairs are read from the calldata
            // run whose bit offset decode_calldata left in the run's image slot.
            let bit := mload(ptr)
            for { let i := 0 } lt(i, total_rounds) { i := add(i, 1) } {
                let zp := add(POINT_PTR(), mul(i, 32))
                let r
                r, claim := factored_round(bit, mload(zp), claim, modulus)
                bit := add(bit, 246)
                mstore(zp, r)
            }
            next_ptr := add(ptr, __TEMPLATE_FACTORED_ROUND_SLOT_BYTES)
            // gkr_dr_final compares the claim directly, so it must be canonical. factored_round already
            // returns it reduced; the explicit mod compiles to cheaper code than omitting it.
            next_claim := mod(claim, modulus)
        }



        // Dim-reducing final step in its own frame to keep the caller stack shallow.
        // `cp` points at the NUM_OUTPUTS [E;2] LSB lines in sorted order. Compute
        // g (products and lookup num/den pairs in the named output layout; running batching powers;
        // boundary permutation on the last layer), check g == claim, absorb the LSB lines,
        // draw r_last + next_batching, interpolate the next claims (sorted order), grow the point.
        // Packed LSB lines have two 128-bit lanes; the three lookup kinds each use two columns.
        // The interpolation challenge and next batching draw are reduced by gkr_dr_final's mod.
        function gkr_dr_final(cp, fs, batching, boundary, claim) -> ncp, nbatch {
            let modulus := mload(P_PTR)
            let SI := GKR_EQ_PTR() // reuse eq scratch as the sorted-index array (NUM_OUTPUTS slots)
            for { let li := 0 } lt(li, __TEMPLATE_GKR_NUM_OUTPUTS) { li := add(li, 1) } {
            mstore(add(SI, mul(li, 32)), li) }
            // Reorder the offset-stored LSB lines into logical (OutputType-group) order so
            // grand-products land at PERM_READ / PERM_WRITE and TEARDOWN / INIT. Generated from the artifact's
            // global_output_map value offsets (iteration order).
            if boundary {
                mstore(add(SI, 0), 2) // logical output 0 maps to address-sorted LSB slot 2
                mstore(add(SI, 32), 3) // logical output 1 maps to address-sorted LSB slot 3
                mstore(add(SI, 64), 0) // logical output 2 maps to address-sorted LSB slot 0
                mstore(add(SI, 96), 1) // logical output 3 maps to address-sorted LSB slot 1
            }
            let g := 0
            let gb := 1
            for { let step := __TEMPLATE_GKR_OUTPUT_PERM_READ } lt(step, add(__TEMPLATE_GKR_OUTPUT_PERM_WRITE, 1)) { step := add(step, 1) } {
                let word := mload(add(cp, mul(mload(add(SI, mul(step, 32))), 32)))
                g := add(mulmod(gb, mulmod(shr(128, word), and(word, MASK), modulus), modulus), g)
                gb := mulmod(gb, batching, modulus)
            }
            for { let pr := 0 } lt(pr, 3) { pr := add(pr, 1) } {
                let wN := mload(add(cp, mul(mload(add(SI, mul(add(__TEMPLATE_GKR_OUTPUT_LOOKUP16_NUM, mul(pr, 2)), 32))), 32)))
                let wD := mload(add(cp, mul(mload(add(SI, mul(add(__TEMPLATE_GKR_OUTPUT_LOOKUP16_DEN, mul(pr, 2)), 32))), 32)))
                let num := add(mulmod(shr(128, wN), and(wD, MASK), modulus), mulmod(and(wN, MASK), shr(128, wD), modulus))
                let den := mulmod(shr(128, wD), and(wD, MASK), modulus)
                g := add(mulmod(gb, num, modulus), g)
                gb := mulmod(gb, batching, modulus)
                g := add(mulmod(gb, den, modulus), g)
                gb := mulmod(gb, batching, modulus)
            }
            for { let step := __TEMPLATE_GKR_OUTPUT_TEARDOWN } lt(step, add(__TEMPLATE_GKR_OUTPUT_INIT, 1)) { step := add(step, 1) } {
                let word := mload(add(cp, mul(mload(add(SI, mul(step, 32))), 32)))
                g := add(mulmod(gb, mulmod(shr(128, word), and(word, MASK), modulus), modulus), g)
                gb := mulmod(gb, batching, modulus)
            }
            if iszero(eq(mod(g, modulus), claim)) {
            revert(0, 0) }
            // absorb the NUM_OUTPUTS [E;2] LSB lines (sorted transcript order), draw r_last +
            // next_batching
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            mcopy(add(GKR_ABS_PTR(), 32), cp, __TEMPLATE_GKR_LSB_LINES_BYTES)
            let seed := keccak256(GKR_ABS_PTR(), add(32, __TEMPLATE_GKR_LSB_LINES_BYTES))
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
            for { let li := 0 } lt(li, __TEMPLATE_GKR_NUM_OUTPUTS) { li := add(li, 1) } {
                let word := mload(add(cp, mul(li, 32)))
                let a := shr(128, word)
                let b := and(word, MASK)
                // this loop reads all NUM_OUTPUTS words (= 2·NUM_OUTPUTS lanes) of the LSB lines
                // absorbed above; gkr_dr_final checks both lanes < P here, making every
                // accepted proof's absorb canonical
                if iszero(lt(a, modulus)) { revert(0, 0) }
                if iszero(lt(b, modulus)) { revert(0, 0) }
                mstore(add(GKR_CLAIMS_PTR(), mul(li, 32)), add(a, mulmod(add(b, sub(modulus, a)), r_last, modulus)))
            }
            ncp := add(cp, __TEMPLATE_GKR_LSB_LINES_BYTES)
        }

        // DIM_REDUCE_LAYERS dim-reducing layers (folding_steps OUTPUT_LOG2 .. trace_log2-1).
        // Reads the NUM_OUTPUTS claims + batching from gkr_init (GKR_CLAIMS_PTR /
        // GKR_BATCHING_PTR); reuses sumcheck_rounds for the monomial rounds.
        function gkr_compress(ptr) -> next_ptr, next_alpha {
            let batching := mload(GKR_BATCHING_PTR())
            for { let k := 0 } lt(k, __TEMPLATE_GKR_DIM_REDUCE_LAYERS) { k := add(k, 1) } {
                let fs := add(__TEMPLATE_GKR_OUTPUT_LOG2, k)
                // initial claim = RLC(claims, batching)
                let claim := 0
                let cb := 1
                for { let c := 0 } lt(c, __TEMPLATE_GKR_NUM_OUTPUTS) { c := add(c, 1) } {
                    claim := add(mulmod(cb, mload(add(GKR_CLAIMS_PTR(), mul(c, 32))), mload(P_PTR)), claim)
                    cb := mulmod(cb, batching, mload(P_PTR))
                }
                // redundant for factored_round, which reduces its own output; removing it saves nothing
                claim := mod(claim, mload(P_PTR))
                ptr, claim := sumcheck_rounds(ptr, claim, fs)
                ptr,
                batching := gkr_dr_final(ptr, fs, batching, eq(add(k, 1), __TEMPLATE_GKR_DIM_REDUCE_LAYERS), claim)
            }
            next_ptr := ptr
            next_alpha := batching
        }

        // Image column indices are GKRAddress offsets (u128 lanes); cache and GATEVAL
        // indices are 32-byte heap slots. Gate relation comments identify input/output indices.
function sumcheck_circuit_layer4(ptr, alpha) -> next_ptr, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim); alpha == this layer's batching.
    let claim := sccl4(alpha)
    // SUMCHECK ROUNDS
    ptr, claim := sumcheck_rounds(ptr, claim, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS)
    
    // POINT CHECK
    let acc := 0
            mstore(CIRCUIT_PTR, ptr)
            acc := scl4_g0(alpha, acc)
    let rhs := mod(acc, mload(P_PTR))
    if iszero(eq(claim, rhs)) { revert(0, 0) }
    
            // sumcheck_circuit_layer4 checks these 12 image lanes < P before returning them
                for { let wk := 0 } lt(wk, 12) { wk := add(wk, 1) } {
                    let cv := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, wk))))
                    if iszero(lt(cv, mload(P_PTR))) { revert(0, 0) }
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), cv)
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw the next batching (cache layers
    // absorb final_step ++ extras in one keccak, THEN draw).
    next_ptr, next_alpha := sumcheck_claims_batch(ptr, 12)
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
            // Batch 10 prior-layer output claims in gate order; count - k is the kth claim from the end.
            function sccl4(alpha) -> claim {
            let src := GKR_CLAIMS_PTR()
            claim := mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_4_CLAIMS, 1))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_4_CLAIMS, 2)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_4_CLAIMS, 3)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_4_CLAIMS, 4)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_4_CLAIMS, 5)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_4_CLAIMS, 6)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_4_CLAIMS, 7)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_4_CLAIMS, 8)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_4_CLAIMS, 9)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_4_CLAIMS, 10)))))
            }
function sumcheck_circuit_layer3(ptr, alpha) -> next_ptr, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim); alpha == this layer's batching.
    let claim := sccl3(alpha)
    // SUMCHECK ROUNDS
    ptr, claim := sumcheck_rounds(ptr, claim, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS)
    
    // POINT CHECK
    let acc := 0
            mstore(CIRCUIT_PTR, ptr)
            acc := scl3_g0(alpha, acc)
    let rhs := mod(acc, mload(P_PTR))
    if iszero(eq(claim, rhs)) { revert(0, 0) }
    
            // sumcheck_circuit_layer3 checks these 18 image lanes < P before returning them
                for { let wk := 0 } lt(wk, 18) { wk := add(wk, 1) } {
                    let cv := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, wk))))
                    if iszero(lt(cv, mload(P_PTR))) { revert(0, 0) }
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), cv)
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw the next batching (cache layers
    // absorb final_step ++ extras in one keccak, THEN draw).
    next_ptr, next_alpha := sumcheck_claims_batch(ptr, 18)
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
            // Batch 12 prior-layer output claims in gate order; count - k is the kth claim from the end.
            function sccl3(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_3_CLAIMS, 1))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_3_CLAIMS, 2)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_3_CLAIMS, 3)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_3_CLAIMS, 4)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_3_CLAIMS, 5)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_3_CLAIMS, 6)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_3_CLAIMS, 7)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_3_CLAIMS, 8)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_3_CLAIMS, 9)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_3_CLAIMS, 10)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_3_CLAIMS, 11)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_3_CLAIMS, 12)))))
            }
function sumcheck_circuit_layer2(ptr, alpha) -> next_ptr, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim); alpha == this layer's batching.
    let claim := sccl2(alpha)
    // SUMCHECK ROUNDS
    ptr, claim := sumcheck_rounds(ptr, claim, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS)
    
    // POINT CHECK
    let acc := 0
            mstore(CIRCUIT_PTR, ptr)
            acc := scl2_g0(alpha, acc)
            acc := scl2_g1(alpha, acc)
    let rhs := mod(acc, mload(P_PTR))
    if iszero(eq(claim, rhs)) { revert(0, 0) }
    
            // sumcheck_circuit_layer2 checks these 26 image lanes < P before returning them
                for { let wk := 0 } lt(wk, 26) { wk := add(wk, 1) } {
                    let cv := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, wk))))
                    if iszero(lt(cv, mload(P_PTR))) { revert(0, 0) }
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), cv)
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw the next batching (cache layers
    // absorb final_step ++ extras in one keccak, THEN draw).
    next_ptr, next_alpha := sumcheck_claims_batch(ptr, 26)
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
        let den_out := mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 10)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 11))))), mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 9)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 11))))), mload(P_PTR)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 10)))))
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
            // Batch 18 prior-layer output claims in gate order; count - k is the kth claim from the end.
            function sccl2(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 1))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 2)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 3)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 4)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 5)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 6)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 7)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 8)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 9)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 10)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 11)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 12)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 13)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 14)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 15)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 16)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 17)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_2_CLAIMS, 18)))))
            }
function sumcheck_circuit_layer1(ptr, alpha) -> next_ptr, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim); alpha == this layer's batching.
    let claim := sccl1(alpha)
    // SUMCHECK ROUNDS
    ptr, claim := sumcheck_rounds(ptr, claim, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS)
    
    // POINT CHECK
    let acc := 0
            mstore(CIRCUIT_PTR, ptr)
            scl1_caches()
            acc := scl1_g0(alpha, acc)
            acc := scl1_g1(alpha, acc)
    let rhs := mod(acc, mload(P_PTR))
    if iszero(eq(claim, rhs)) { revert(0, 0) }
    
            // sumcheck_circuit_layer1 checks these 74 image lanes < P before returning them
                for { let wk := 0 } lt(wk, 74) { wk := add(wk, 1) } {
                    let cv := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, wk))))
                    if iszero(lt(cv, mload(P_PTR))) { revert(0, 0) }
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), cv)
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw the next batching (cache layers
    // absorb final_step ++ extras in one keccak, THEN draw).
    {
            let base := mload(CIRCUIT_PTR)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            let bp := add(GKR_ABS_PTR(), 32)
            // absorb final_step ++ extras contiguously, then draw (soundness: batching depends on
            // the extra cache-dependency evals). ONE keccak of [seed || final_step || extras].
            // Copy 8 u128 image lanes starting at lane 0; each lane is 16 bytes.
            mcopy(bp, add(base, mul(16, 0)), mul(16, 8))
            bp := add(bp, mul(16, 8))
            // Copy 26 u128 image lanes starting at lane 48; each lane is 16 bytes.
            mcopy(bp, add(base, mul(16, 48)), mul(16, 26))
            bp := add(bp, mul(16, 26))
            // Cache slot 0: scl1_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)))))
            bp := add(bp, 16)
            // Cache slot 1: scl1_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)))))
            bp := add(bp, 16)
            // Cache slot 2: scl1_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)))))
            bp := add(bp, 16)
            // Cache slot 3: scl1_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)))))
            bp := add(bp, 16)
            // Cache slot 4: scl1_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)))))
            bp := add(bp, 16)
            // Copy 40 u128 image lanes starting at lane 8; each lane is 16 bytes.
            mcopy(bp, add(base, mul(16, 8)), mul(16, 40))
            bp := add(bp, mul(16, 40))
            let s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR()))
            mstore(SEED_PTR(), s)
            s := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), s)
            next_alpha := mod(shr(128, s), mload(P_PTR))
            next_ptr := add(ptr, mul(16, 74))
            }
}

            function scl1_caches() {
    {  // VectorizedLookup: (1[9]) + (1[10]) + (1[11]) + (0) + (0) + (0) + (0) + (0) + (0) + (1[8]) = Cache(0)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 8))))), 0), 0), 0), 0), 0), 0), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 11))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 10))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 9)))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (1[13]) + (1[14]) + (1[15]) + (1[16]) + (1[17]) + (1[18]) + (1[19]) + (1[20]) + (0) + (1[12]) = Cache(1)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 12))))), 0), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 20))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 19))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 18))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 17))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 16))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 15))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 14))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 13)))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (1[22]) + (1[23]) + (1[24]) + (1[25]) + (1[26]) + (1[27]) + (1[28]) + (1[29]) + (0) + (1[21]) = Cache(2)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 21))))), 0), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 29))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 28))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 27))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 26))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 23))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 22)))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (1[31]) + (1[32]) + (1[33]) + (1[34]) + (1[35]) + (1[36]) + (1[37]) + (1[38]) + (0) + (1[30]) = Cache(3)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 30))))), 0), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 38))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 37))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 36))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 35))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 34))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 33))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 32))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 31)))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (1[40]) + (1[41]) + (1[42]) + (1[43]) + (1[44]) + (1[45]) + (1[46]) + (1[47]) + (0) + (1[39]) = Cache(4)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 39))))), 0), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 47))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 46))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 45))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 44))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 43))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 42))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 41))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 40)))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)), mod(gate, mload(P_PTR)))
    }
            }
            function scl1_g0(alpha, a) -> acc { acc := a
    // CopyInExtensionField: [5] = 25
    acc := gate_copyinextensionfield(alpha, acc, 5)
    
    // CopyInExtensionField: [6] = 24
    acc := gate_copyinextensionfield(alpha, acc, 6)
    
    {  // LookupUnbalancedPairWithMaterializedVectorInputs: [72]/[73] + 1/(δ + Cache(4)) = 22/23
        let den_out := mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 73)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)))), mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 72)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)))), mload(P_PTR)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 73)))))
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
        let den_out := mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 70)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 71))))), mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 69)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 71))))), mload(P_PTR)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 70)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // CopyInBaseField: [7] = 11
        let gate := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 7))))
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
        let den_out := mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 61)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 62))))), mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 60)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 62))))), mload(P_PTR)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 61)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // TrivialProduct: [2]*[4] = 2
        let gate := mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 4)))), mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // TrivialProduct: [1]*[3] = 1
        let gate := mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 1)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 3)))), mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // CopyInBaseField: [0] = 0
        let gate := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 0))))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
            }
            // Batch 26 prior-layer output claims in gate order; count - k is the kth claim from the end.
            function sccl1(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 1))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 2)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 3)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 4)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 5)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 6)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 7)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 8)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 9)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 10)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 11)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 12)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 13)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 14)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 15)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 16)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 17)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 18)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 19)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 20)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 21)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 22)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 23)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 24)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 25)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_1_CLAIMS, 26)))))
            }
function sumcheck_circuit_layer0(ptr, alpha) -> next_ptr {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim); alpha == this layer's batching.
    let claim := sccl0(alpha)
    // SUMCHECK ROUNDS
    ptr, claim := sumcheck_rounds(ptr, claim, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS)
    
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
            mstore(add(GKR_GATEVAL_PTR(), mul(32, 29)), 0x380000000000000000000000000) // gate slot 29: relation constant via Proth120::to_u128
            mstore(add(GKR_GATEVAL_PTR(), mul(32, 30)), 0x37ffe4000000000000000000000) // gate slot 30: relation constant via Proth120::to_u128
            mstore(add(GKR_GATEVAL_PTR(), mul(32, 77)), 0x7800000100000000) // gate slot 77: relation constant via Proth120::to_u128
            codecopy(GKR_QTABLE_PTR(), add(mload(SETUP_CODE_OFFSET_PTR), __TEMPLATE_DATA_QTABLE_OFFSET), __TEMPLATE_DATA_QTABLE_BYTES)
            // accumulate every term into gateval[gate_slot], one loop per bucket
            {
            let modulus := P
            let col_base := mload(CIRCUIT_PTR) // image address of the column at-point evals
            let gateval := GKR_GATEVAL_PTR()
            // Record byte 0: gate slot; byte 1: column a; quadratic byte 2: column b.
            // linear    terms, coeff  1B positive  (68 records); QTABLE bytes [0, 204), 3 bytes per record.
            // Coefficient at byte 2, width 1, mask 0xff; shift 232 = 8*(32-2-1).
            { let rec_ptr := add(GKR_QTABLE_PTR(), 0) let rec_end := add(rec_ptr, 204)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 3) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(232, rec), 0xff), shr(128, mload(add(col_base, mul(16, byte(1, rec))))), modulus), modulus))
            } }
            // linear    terms, coeff  2B positive  (4 records); QTABLE bytes [204, 220), 4 bytes per record.
            // Coefficient at byte 2, width 2, mask 0xffff; shift 224 = 8*(32-2-2).
            { let rec_ptr := add(GKR_QTABLE_PTR(), 204) let rec_end := add(rec_ptr, 16)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 4) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(224, rec), 0xffff), shr(128, mload(add(col_base, mul(16, byte(1, rec))))), modulus), modulus))
            } }
            // linear    terms, coeff 16B canonical (Proth120::to_u128) (6 records); QTABLE bytes [220, 328), 18 bytes per record.
            // Coefficient at byte 2, width 16, mask MASK; shift 112 = 8*(32-2-16).
            { let rec_ptr := add(GKR_QTABLE_PTR(), 220) let rec_end := add(rec_ptr, 108)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 18) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(112, rec), MASK), shr(128, mload(add(col_base, mul(16, byte(1, rec))))), modulus), modulus))
            } }
            // linear    terms, coeff  1B negative  (59 records); QTABLE bytes [328, 505), 3 bytes per record.
            // Coefficient at byte 2, width 1, mask 0xff; shift 232 = 8*(32-2-1).
            { let rec_ptr := add(GKR_QTABLE_PTR(), 328) let rec_end := add(rec_ptr, 177)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 3) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(sub(modulus, and(shr(232, rec), 0xff)), shr(128, mload(add(col_base, mul(16, byte(1, rec))))), modulus), modulus))
            } }
            // quadratic terms, coeff  1B positive  (328 records); QTABLE bytes [505, 1817), 4 bytes per record.
            // Coefficient at byte 3, width 1, mask 0xff; shift 224 = 8*(32-3-1).
            { let rec_ptr := add(GKR_QTABLE_PTR(), 505) let rec_end := add(rec_ptr, 1312)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 4) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(224, rec), 0xff), mulmod(shr(128, mload(add(col_base, mul(16, byte(1, rec))))), shr(128, mload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff  2B positive  (16 records); QTABLE bytes [1817, 1897), 5 bytes per record.
            // Coefficient at byte 3, width 2, mask 0xffff; shift 216 = 8*(32-3-2).
            { let rec_ptr := add(GKR_QTABLE_PTR(), 1817) let rec_end := add(rec_ptr, 80)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 5) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(216, rec), 0xffff), mulmod(shr(128, mload(add(col_base, mul(16, byte(1, rec))))), shr(128, mload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff  4B positive  (14 records); QTABLE bytes [1897, 1995), 7 bytes per record.
            // Coefficient at byte 3, width 4, mask 0xffffffff; shift 200 = 8*(32-3-4).
            { let rec_ptr := add(GKR_QTABLE_PTR(), 1897) let rec_end := add(rec_ptr, 98)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 7) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(200, rec), 0xffffffff), mulmod(shr(128, mload(add(col_base, mul(16, byte(1, rec))))), shr(128, mload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff 16B canonical (Proth120::to_u128) (30 records); QTABLE bytes [1995, 2565), 19 bytes per record.
            // Coefficient at byte 3, width 16, mask MASK; shift 104 = 8*(32-3-16).
            { let rec_ptr := add(GKR_QTABLE_PTR(), 1995) let rec_end := add(rec_ptr, 570)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 19) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(104, rec), MASK), mulmod(shr(128, mload(add(col_base, mul(16, byte(1, rec))))), shr(128, mload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff  1B negative  (113 records); QTABLE bytes [2565, 3017), 4 bytes per record.
            // Coefficient at byte 3, width 1, mask 0xff; shift 224 = 8*(32-3-1).
            { let rec_ptr := add(GKR_QTABLE_PTR(), 2565) let rec_end := add(rec_ptr, 452)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 4) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(sub(modulus, and(shr(224, rec), 0xff)), mulmod(shr(128, mload(add(col_base, mul(16, byte(1, rec))))), shr(128, mload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff  4B negative  (48 records); QTABLE bytes [3017, 3353), 7 bytes per record.
            // Coefficient at byte 3, width 4, mask 0xffffffff; shift 200 = 8*(32-3-4).
            { let rec_ptr := add(GKR_QTABLE_PTR(), 3017) let rec_end := add(rec_ptr, 336)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 7) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(sub(modulus, and(shr(200, rec), 0xffffffff)), mulmod(shr(128, mload(add(col_base, mul(16, byte(1, rec))))), shr(128, mload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
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
    let rhs := mod(acc, mload(P_PTR))
    if iszero(eq(claim, rhs)) { revert(0, 0) }
    
            // sumcheck_circuit_layer0 checks all 106 base-layer image lanes < P here before
            // returning to emit_gkr_mark, making the absorbed transcript bytes canonical
                for { let wk := 0 } lt(wk, 106) { wk := add(wk, 1) } {
                    if iszero(lt(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, wk)))), mload(P_PTR))) { revert(0, 0) }
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw the next batching (cache layers
    // absorb final_step ++ extras in one keccak, THEN draw).
    {
            let base := mload(CIRCUIT_PTR)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            let bp := add(GKR_ABS_PTR(), 32)
            // absorb final_step ++ extras contiguously, then draw (soundness: batching depends on
            // the extra cache-dependency evals). ONE keccak of [seed || final_step || extras].
            // Copy 58 u128 image lanes starting at lane 38; each lane is 16 bytes.
            mcopy(bp, add(base, mul(16, 38)), mul(16, 58))
            bp := add(bp, mul(16, 58))
            // Copy 2 u128 image lanes starting at lane 2; each lane is 16 bytes.
            mcopy(bp, add(base, mul(16, 2)), mul(16, 2))
            bp := add(bp, mul(16, 2))
            // Copy 7 u128 image lanes starting at lane 5; each lane is 16 bytes.
            mcopy(bp, add(base, mul(16, 5)), mul(16, 7))
            bp := add(bp, mul(16, 7))
            // Copy 24 u128 image lanes starting at lane 14; each lane is 16 bytes.
            mcopy(bp, add(base, mul(16, 14)), mul(16, 24))
            bp := add(bp, mul(16, 24))
            // Cache slot 16: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)))))
            bp := add(bp, 16)
            // Cache slot 17: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)))))
            bp := add(bp, 16)
            // Cache slot 18: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18)))))
            bp := add(bp, 16)
            // Cache slot 19: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19)))))
            bp := add(bp, 16)
            // Cache slot 0: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)))))
            bp := add(bp, 16)
            // Cache slot 1: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)))))
            bp := add(bp, 16)
            // Cache slot 2: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)))))
            bp := add(bp, 16)
            // Cache slot 3: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)))))
            bp := add(bp, 16)
            // Cache slot 4: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)))))
            bp := add(bp, 16)
            // Cache slot 5: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 5)))))
            bp := add(bp, 16)
            // Cache slot 6: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 6)))))
            bp := add(bp, 16)
            // Cache slot 7: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 7)))))
            bp := add(bp, 16)
            // Cache slot 8: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 8)))))
            bp := add(bp, 16)
            // Cache slot 9: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 9)))))
            bp := add(bp, 16)
            // Cache slot 10: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 10)))))
            bp := add(bp, 16)
            // Cache slot 11: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 11)))))
            bp := add(bp, 16)
            // Cache slot 12: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 12)))))
            bp := add(bp, 16)
            // Cache slot 13: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 13)))))
            bp := add(bp, 16)
            // Cache slot 14: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 14)))))
            bp := add(bp, 16)
            // Cache slot 15: scl0_caches stores mod(gate, mload(P_PTR)); absorb one high u128 lane.
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 15)))))
            bp := add(bp, 16)
            // Copy 2 u128 image lanes starting at lane 0; each lane is 16 bytes.
            mcopy(bp, add(base, mul(16, 0)), mul(16, 2))
            bp := add(bp, mul(16, 2))
            // Copy 1 u128 image lanes starting at lane 4; each lane is 16 bytes.
            mcopy(bp, add(base, mul(16, 4)), mul(16, 1))
            bp := add(bp, mul(16, 1))
            // Copy 2 u128 image lanes starting at lane 12; each lane is 16 bytes.
            mcopy(bp, add(base, mul(16, 12)), mul(16, 2))
            bp := add(bp, mul(16, 2))
            // Copy 10 u128 image lanes starting at lane 96; each lane is 16 bytes.
            mcopy(bp, add(base, mul(16, 96)), mul(16, 10))
            bp := add(bp, mul(16, 10))
            let s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR()))
            mstore(SEED_PTR(), s)
            s := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), s)
            next_ptr := add(ptr, mul(16, 106))
            }
}

            function scl0_caches() {
    {  // MemoryTuple: (γ + 0 + α[4] + α²0 + α³([0]) + α⁴[1] + α⁵[2] + α⁶[3]) = Cache(0)
        let gate := add(gkr_memrel_compress_low(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 4)))), 0), gkr_memrel_compress_high(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 0)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 1)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 3))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + [9] + α[10] + α²[11] + α³([5]) + α⁴[6] + α⁵[7] + α⁶[8]) = Cache(1)
        let gate := add(gkr_memrel_compress_low(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 10)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 11))))), gkr_memrel_compress_high(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 5)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 6)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 7)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 8))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + 0 + α[4] + α²0 + α³([24]) + α⁴[25] + α⁵[2] + α⁶[3]) = Cache(2)
        let gate := add(gkr_memrel_compress_low(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 4)))), 0), gkr_memrel_compress_high(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 3))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + [9] + α[10] + α²[11] + α³(1 + [24]) + α⁴[25] + α⁵[7] + α⁶[8]) = Cache(3)
        let gate := add(gkr_memrel_compress_low(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 10)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 11))))), gkr_memrel_compress_high(add(1, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 7)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 8))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + [16] + α[17] + α²[18] + α³([12]) + α⁴[13] + α⁵[14] + α⁶[15]) = Cache(4)
        let gate := add(gkr_memrel_compress_low(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 17)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 18))))), gkr_memrel_compress_high(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 12)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 13)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 14)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 15))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + 2 + α0 + α²0 + α³([24]) + α⁴[25] + α⁵[22] + α⁶[23]) = Cache(5)
        let gate := add(gkr_memrel_compress_low(2, 0, 0), gkr_memrel_compress_high(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 22)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 23))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 5)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + [16] + α[17] + α²[18] + α³(2 + [24]) + α⁴[25] + α⁵[19] + α⁶[20]) = Cache(6)
        let gate := add(gkr_memrel_compress_low(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 17)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 18))))), gkr_memrel_compress_high(add(2, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 19)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 20))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 6)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + 2 + α0 + α²0 + α³([28]) + α⁴[29] + α⁵[26] + α⁶[27]) = Cache(7)
        let gate := add(gkr_memrel_compress_low(2, 0, 0), gkr_memrel_compress_high(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 28)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 29)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 26)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 27))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 7)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: -1[24] + 1[0] + 2^19[90] = Cache(8)
        let gate := add(add(mulmod(sub(mload(P_PTR), 1), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24)))), mload(P_PTR)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 0))))), mulmod(524288, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 90)))), mload(P_PTR)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 8)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: 2^19 + -1[25] + 1[1] + -1[90] = Cache(9)
        let gate := add(524288, add(add(mulmod(sub(mload(P_PTR), 1), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25)))), mload(P_PTR)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 1))))), mulmod(sub(mload(P_PTR), 1), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 90)))), mload(P_PTR))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 9)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: -1 + -1[24] + 1[5] + 2^19[91] = Cache(10)
        let gate := add(sub(mload(P_PTR), 1), add(add(mulmod(sub(mload(P_PTR), 1), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24)))), mload(P_PTR)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 5))))), mulmod(524288, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 91)))), mload(P_PTR))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 10)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: 2^19 + -1[25] + 1[6] + -1[91] = Cache(11)
        let gate := add(524288, add(add(mulmod(sub(mload(P_PTR), 1), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25)))), mload(P_PTR)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 6))))), mulmod(sub(mload(P_PTR), 1), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 91)))), mload(P_PTR))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 11)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: -2 + -1[24] + 1[12] + 2^19[92] = Cache(12)
        let gate := add(sub(mload(P_PTR), 2), add(add(mulmod(sub(mload(P_PTR), 1), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24)))), mload(P_PTR)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 12))))), mulmod(524288, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 92)))), mload(P_PTR))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 12)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: 2^19 + -1[25] + 1[13] + -1[92] = Cache(13)
        let gate := add(524288, add(add(mulmod(sub(mload(P_PTR), 1), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25)))), mload(P_PTR)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 13))))), mulmod(sub(mload(P_PTR), 1), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 92)))), mload(P_PTR))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 13)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (1[22]) + (1[23]) + (1[4]) + (1[38]) + (1[39]) + (1[40]) + (1[41]) + (1[42]) + (1[43] + 2[44] + 2^2[45] + 2^3[46] + 2^4[47] + 2^5[48] + 2^6[49] + 2^7[50] + 2^8[51] + 2^9[52] + 2^10[53] + 2^11[54] + 2^12[55] + 2^13[56] + 2^14[57] + 2^15[58] + 2^16[59] + 2^17[9] + 2^18[16]) + (46) = Cache(14)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, 46), add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 43)))), mulmod(2, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 44)))), mload(P_PTR))), mulmod(4, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 45)))), mload(P_PTR))), mulmod(8, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 46)))), mload(P_PTR))), mulmod(16, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 47)))), mload(P_PTR))), mulmod(32, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 48)))), mload(P_PTR))), mulmod(64, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 49)))), mload(P_PTR))), mulmod(128, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mload(P_PTR))), mulmod(256, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 51)))), mload(P_PTR))), mulmod(512, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 52)))), mload(P_PTR))), mulmod(1024, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mload(P_PTR))), mulmod(2048, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mload(P_PTR))), mulmod(4096, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mload(P_PTR))), mulmod(8192, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mload(P_PTR))), mulmod(16384, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 57)))), mload(P_PTR))), mulmod(32768, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mload(P_PTR))), mulmod(65536, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mload(P_PTR))), mulmod(131072, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mload(P_PTR))), mulmod(262144, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mload(P_PTR)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 42))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 41))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 40))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 39))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 38))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 4))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 23))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 22)))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 14)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookupSetup: β⁰[96] + β¹[97] + β²[98] + β³[99] + β⁴[100] + β⁵[101] + β⁶[102] + β⁷[103] + β⁸[104] + β⁹[105] = Cache(15)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 105))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 104))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 103))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 102))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 101))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 100))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 99))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 98))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 97))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 96)))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 15)), mod(gate, mload(P_PTR)))
    }
    {  // RangeCheck16Bits: (Σ_{k<16} 2^k·r[k]) · Π_{k≥16} (1 − r[k]) = Cache(16)
        let gate := gkr_virtual_poly_rangecheck(16)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)), mod(gate, mload(P_PTR)))
    }
    {  // RangeCheckTimestamp: (Σ_{k<19} 2^k·r[k]) · Π_{k≥19} (1 − r[k]) = Cache(17)
        let gate := gkr_virtual_poly_rangecheck(19)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)), mod(gate, mload(P_PTR)))
    }
    {  // InitsAndTeardownsLow: 4·Σ_{k<14} 2^k·r[k] = Cache(18)
        let gate := mul(4, gkr_virtual_poly_compose_vars(14, 0)) // u32 word-aligned
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18)), mod(gate, mload(P_PTR)))
    }
    {  // InitsAndTeardownsHigh: Σ_{k<8} 2^k·r[14 + k] = Cache(19)
        let gate := gkr_virtual_poly_compose_vars(8, 14)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19)), mod(gate, mload(P_PTR)))
    }
            }
            function scl0_g0(alpha, a) -> acc { acc := a
            // Horner over consecutive GATEVAL slots [0, 12); each slot is one 32-byte word.
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 0 } lt(s, 12) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g1(alpha, a) -> acc { acc := a
            // Horner over consecutive GATEVAL slots [12, 24); each slot is one 32-byte word.
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 12 } lt(s, 24) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g2(alpha, a) -> acc { acc := a
            // Horner over consecutive GATEVAL slots [24, 36); each slot is one 32-byte word.
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 24 } lt(s, 36) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g3(alpha, a) -> acc { acc := a
            // Horner over consecutive GATEVAL slots [36, 48); each slot is one 32-byte word.
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 36 } lt(s, 48) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g4(alpha, a) -> acc { acc := a
            // Horner over consecutive GATEVAL slots [48, 60); each slot is one 32-byte word.
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 48 } lt(s, 60) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g5(alpha, a) -> acc { acc := a
            // Horner over consecutive GATEVAL slots [60, 72); each slot is one 32-byte word.
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 60 } lt(s, 72) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g6(alpha, a) -> acc { acc := a
            // Horner over consecutive GATEVAL slots [72, 79); each slot is one 32-byte word.
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 72 } lt(s, 79) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

    {  // LookupWithCachedDensAndSetup: (([21])·((Cache(15))+δ) − ([95])·((Cache(14))+δ)) / (((Cache(14))+δ)((Cache(15))+δ)) = 72/73
        let bg := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 14))))
        let dg := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 15))))
        let den_out := mulmod(bg, dg, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 21)))), dg, mload(P_PTR)), sub(mul(2, mload(P_PTR)), mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 95)))), bg, mload(P_PTR))))
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
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 29)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 8))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
            }
            function scl0_g7(alpha, a) -> acc { acc := a
    {  // LookupFromMaterializedBaseInputWithSetup: 1/(δ + [28]) - [94]/(δ + Cache(17)) = 63/64
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 28))))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)))), mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)))), sub(mload(P_PTR), mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 94)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 28))))), mload(P_PTR))))
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // CopyInBaseField: [27] = 62
        let gate := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 27))))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[18]) + 1/(δ+[26]) = 60/61
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 18)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 26)))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[11]) + 1/(δ+[17]) = 58/59
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 11)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 17)))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[72]) + 1/(δ+[10]) = 56/57
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 72)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 10)))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[66]) + 1/(δ+[23]) = 54/55
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 66)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 23)))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[20]) + 1/(δ+[65]) = 52/53
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 20)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 65)))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[83]) + 1/(δ+[19]) = 50/51
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 83)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 19)))))
        let den_out := mulmod(den1, den2, mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // LookupFromMaterializedBaseInputWithSetup: 1/(δ + [82]) - [93]/(δ + Cache(16)) = 48/49
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 82))))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)))), mload(P_PTR))
        let gate := den_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)))), sub(mload(P_PTR), mulmod(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 93)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 82))))), mload(P_PTR))))
        gate := num_out
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
            // Horner over consecutive GATEVAL slots [79, 82); each slot is one 32-byte word.
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 79 } lt(s, 82) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g8(alpha, a) -> acc { acc := a
            // Horner over consecutive GATEVAL slots [82, 94); each slot is one 32-byte word.
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 82 } lt(s, 94) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g9(alpha, a) -> acc { acc := a
            // Horner over consecutive GATEVAL slots [94, 106); each slot is one 32-byte word.
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 94 } lt(s, 106) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g10(alpha, a) -> acc { acc := a
            // Horner over consecutive GATEVAL slots [106, 118); each slot is one 32-byte word.
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 106 } lt(s, 118) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g11(alpha, a) -> acc { acc := a
            // Horner over consecutive GATEVAL slots [118, 120); each slot is one 32-byte word.
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 118 } lt(s, 120) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[0]<<8)) + α³[32] + α⁴[33] + α⁵[30] + α⁶[31]) * (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[1]<<8)) + α³[36] + α⁴[37] + α⁵[34] + α⁶[35]) = 6
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR(), mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))), mload(P_PTR)))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(8, __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_0)), mload(P_PTR)), gkr_memrel_compress_high(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 32)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 33)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 30)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 31)))))))
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(8, __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_1)), mload(P_PTR)), gkr_memrel_compress_high(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 36)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 37)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 34)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 35)))))))
        let gate := mulmod(lhs, rhs, mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[0]<<8)) + 0) * (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[1]<<8)) + 0) = 5
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR(), mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))), mload(P_PTR)))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(8, __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_0)), mload(P_PTR)), 0))
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(8, __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_1)), mload(P_PTR)), 0))
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
        let gate := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 21))))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
            }
            // Batch 74 prior-layer output claims in gate order; count - k is the kth claim from the end.
            function sccl0(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 1))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 2)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 3)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 4)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 5)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 6)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 7)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 8)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 9)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 10)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 11)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 12)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 13)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 14)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 15)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 16)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 17)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 18)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 19)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 20)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 21)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 22)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 23)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 24)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 25)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 26)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 27)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 28)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 29)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 30)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 31)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 32)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 33)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 34)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 35)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 36)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 37)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 38)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 39)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 40)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 41)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 42)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 43)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 44)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 45)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 46)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 47)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 48)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 49)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 50)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 51)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 52)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 53)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 54)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 55)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 56)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 57)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 58)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 59)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 60)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 61)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 62)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 63)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 64)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 65)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 66)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 67)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 68)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 69)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 70)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 71)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 72)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 73)))))
            claim := add(mulmod(claim, alpha, mload(P_PTR)), mload(add(src, mul(32, sub(__TEMPLATE_GKR_LAYER_0_CLAIMS, 74)))))
            }
// points u128 lanes follow a 32-byte seed; shr(128) selects a lane from the fresh digest.
function sumcheck_claims_batch(ptr, points) -> next_ptr, next_alpha {
    let input_bytes := mul(points, 16)
    mcopy(add(SEED_PTR(), 32), ptr, input_bytes)
    let seed := keccak256(SEED_PTR(), add(32, input_bytes)) // absorb evals
    mstore(SEED_PTR(), seed)
    seed := keccak256(SEED_PTR(), 32)                       // draw (the mirror draws a fresh el)
    mstore(SEED_PTR(), seed)
    next_alpha := mod(shr(128, seed), mload(P_PTR))                    // sumcheck_claims_batch reduces the draw with mod
    next_ptr := add(ptr, input_bytes)
}

// One β-Horner step: acc·β + c. Callers chain ten of these (see lookrel_horner),
// keeping every call boundary at 2 args so the enclosing cache/gate function stays
// inside the EVM stack limit.
function gkr_lookrel_step(acc, c) -> acc_next {
    acc_next := add(mulmod(acc, mload(LOGUP_CHALLS_PTR()), mload(P_PTR)), c)
}

// Split memrel into a 3-arg low + 4-arg high, composed by the caller as
// add(low(...), high(...)). A single 7-arg helper would make solc materialize all 7
// expression-args at the call boundary, running the enclosing cache function 1 slot
// too deep (the same failure the lookrel steps above avoid).
// Memory challenge byte offsets 0/32 weight address limbs; 64/96 timestamp limbs;
// 128/160 value limbs; 192 is the additive challenge (slots 0 through 6).
function gkr_memrel_compress_low(address_space, addr_low, addr_high) -> compressed {
    compressed := add(mload(add(MEMORY_CHALLS_PTR(), 192)), address_space)
    compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR()), addr_low, mload(P_PTR)))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 32)), addr_high, mload(P_PTR)))
}
function gkr_memrel_compress_high(ts_low, ts_high, val_low, val_high) -> compressed {
    compressed := mulmod(mload(add(MEMORY_CHALLS_PTR(), 64)), ts_low, mload(P_PTR))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 96)), ts_high, mload(P_PTR)))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 128)), val_low, mload(P_PTR)))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 160)), val_high, mload(P_PTR)))
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

function gate_image_load(idx) -> load {
    load := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, idx))))
}
function pointcheck_update(acc, alpha, gate) -> next_acc {
    next_acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
}
function logup_pointcheck_update(acc, alpha, num_out, den_out) -> next_acc {
    acc := pointcheck_update(acc, alpha, den_out)
    next_acc := pointcheck_update(acc, alpha, num_out)
}

function gate_aggregatelookuprationalpair(alpha, acc, num1_idx, num2_idx, den1_idx, den2_idx) -> next_acc {
    let num1 := gate_image_load(num1_idx)
    let num2 := gate_image_load(num2_idx)
    let den1 := gate_image_load(den1_idx)
    let den2 := gate_image_load(den2_idx)
    let den_out := mulmod(den1, den2, mload(P_PTR))
    let num_out := add(mulmod(num1, den2, mload(P_PTR)), mulmod(num2, den1, mload(P_PTR)))
    next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
}
function gate_copyinextensionfield(alpha, acc, input_idx) -> next_acc {
    let input := gate_image_load(input_idx)
    next_acc := pointcheck_update(acc, alpha, input)
}

function gate_maskintoidentityproduct(alpha, acc, input_idx, mask_idx) -> next_acc {
    let input := gate_image_load(input_idx)
    let mask := gate_image_load(mask_idx)
    let neg_one := sub(mload(P_PTR), 1)
    let gate := add(mulmod(mask, add(input, neg_one), mload(P_PTR)), 1)
    next_acc := pointcheck_update(acc, alpha, gate)
}

        // Circuit sumcheck: run every circuit layer from the output layer (highest index,
        // reads the dim-reduce output GKR_CLAIMS_PTR) down to layer 0. The call sequence is
        // generated from the artifact's layer count so it can't drift when the circuit gains
        // or loses a layer — see gkr_circuit_layer_calls in the generator.
        function gkr_circuit(ptr, alpha) -> next_ptr {
            // Generated calls thread (ptr, alpha) through layers N down to 1; layer 0
            // consumes the final alpha and returns only ptr.
            ptr, alpha := sumcheck_circuit_layer4(ptr, alpha)
            ptr, alpha := sumcheck_circuit_layer3(ptr, alpha)
            ptr, alpha := sumcheck_circuit_layer2(ptr, alpha)
            ptr, alpha := sumcheck_circuit_layer1(ptr, alpha)
            ptr := sumcheck_circuit_layer0(ptr, alpha)
            next_ptr := ptr
        }

        // Interpolate-halve n elements at sc: sc[j] = sc[2j] + (sc[2j+1]-sc[2j])·r.
        // Two adjacent 32-byte elements per pair give a 64-byte source stride; n/2 pairs remain.
        function whir_foldhalf(sc, n, r) {
            // sumcheck_circuit_layer0 checks the input lanes < P before emit_gkr_mark calls here.
            // whir_fold_pack supplies zero padding; earlier whir_foldhalf outputs use addmod.
            // Thus sub(Pm, a) is valid. Packing coordinates are reduced by emit_gkr_mark's mod.
            let Pm := mload(P_PTR)
            for { let j := 0 } lt(j, div(n, 2)) { j := add(j, 1) } {
                let a := mload(add(sc, mul(64, j)))
                let b := mload(add(sc, add(mul(64, j), 32)))
                mstore(add(sc, mul(32, j)), addmod(a, mulmod(addmod(b, sub(Pm, a), Pm), r, Pm), Pm))
            }
        }
        // Fold one PACK = 2^PACK_LOG2 chunk (count real evals from the image, rest zero) by the
        // PACK_LOG2 packing coords at `ex` — a PACK_LOG2-var multilinear eval → single claim.
        // LSB binding: adjacent evals differ in pack-index bit 0, which pairs with ex[0], so the
        // coords apply FORWARD (mirrors the prover's merge_claims). Scratch: PACK slots at
        // ABS+FOLD_OFFSET (the generator sizes the ABS region for it).
        // u128 image lanes are unpacked with a 128-bit shift; absent packing lanes are zero.
        function whir_fold_pack(cdbase, count, ex) -> v {
            let sc := add(GKR_ABS_PTR(), __TEMPLATE_GKR_HANDOFF_FOLD_OFFSET)
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_PACK) { i := add(i, 1) } {
                let val := 0
                if lt(i, count) {
                val := shr(128, mload(add(cdbase, mul(16, i)))) }
                mstore(add(sc, mul(32, i)), val)
            }
            let n := __TEMPLATE_WHIR_PACK
            for { let k := 0 } lt(k, __TEMPLATE_WHIR_PACK_LOG2) { k := add(k, 1) } {
                whir_foldhalf(sc, n, mload(add(ex, mul(32, k))))
                n := shr(1, n)
            }
            v := mload(sc)
        }
        // bytes32 from MARK_WORD_REGISTERS consecutive final registers' u32 values (each stored
        // LE at preimage byte reg*PREIMAGE_REGISTER_STRIDE; the preimage starts the image),
        // concatenated in register order. Assembled in the 0x00 scratch word.
        // Each public register is a 4-byte LE u32, packed contiguously into one EVM word.
        function mark_word(first_reg) -> w {
            for { let i := 0 } lt(i, MARK_WORD_REGISTERS) { i := add(i, 1) } {
                mcopy(mul(i, 4), add(IMAGE_PTR(), mul(add(first_reg, i), PREIMAGE_REGISTER_STRIDE)), 4)
            }
            w := mload(0)
        }

        // GKR→WHIR handoff: draw the PACK_LOG2 packing coords, merge the base-layer claims
        // (mem++wit NUM_MEMWIT→MERGED_MW, setup NUM_SETUP→SETUP_MERGED), draw the WHIR batching challenge
        // (PoW), form the batched opening, and write the WHIR half's start state straight into
        // its memory regions: seed, gamma powers, opening, z = base_z(BASE_Z_COORDS) ++
        // extra(PACK_LOG2) (the pack index occupies the HIGH bits of the packed enumeration, so
        // under LSB binding the packing coords EXTEND the claim point at the top). decode_calldata
        // already wrote the memory base-oracle cap. Own frame — keeps the fallback stack under the
        // EVM limit. `ptr` is the image cursor after the circuit layers: it points at the 8-byte
        // WHIR-batching PoW nonce.
        // Each draw reduces the high 128 bits using mod. PoW hashes seed32 || nonce8 (40 bytes);
        // 256 is the digest bit width used by the leading-zero check.
        function emit_gkr_mark(ptr) {
            let sp := SEED_PTR()
            // ABS-region scratch (sized by the generator): PACK_LOG2 packing coords at +0,
            // MERGED_MW + SETUP_MERGED merged claims at +MERGED_OFFSET, whir_fold_pack's chunk
            // buffer at +FOLD_OFFSET.
            let ex := GKR_ABS_PTR()
            let mg := add(GKR_ABS_PTR(), __TEMPLATE_GKR_HANDOFF_MERGED_OFFSET)
            // draw PACK_LOG2 packing coords
            let seed := mload(sp)
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_PACK_LOG2) { i := add(i, 1) } {
                seed := keccak256(sp, 32)
                mstore(sp, seed)
                mstore(add(ex, mul(32, i)), mod(shr(128, seed), mload(P_PTR)))
            }
            // merge base-layer claims (dense in layer0's eval block at CIRCUIT_PTR): the
            // mem++wit groups, then the setup groups (columns NUM_MEMWIT..), each zero-padded
            for { let g := 0 } lt(g, add(__TEMPLATE_WHIR_MERGED_MW, __TEMPLATE_WHIR_SETUP_MERGED)) { g := add(g, 1) } {
                let col := mul(g, __TEMPLATE_WHIR_PACK)
                let limit := __TEMPLATE_WHIR_NUM_MEMWIT
                if iszero(lt(g, __TEMPLATE_WHIR_MERGED_MW)) {
                    col := add(__TEMPLATE_WHIR_NUM_MEMWIT, mul(sub(g, __TEMPLATE_WHIR_MERGED_MW), __TEMPLATE_WHIR_PACK))
                    limit := add(__TEMPLATE_WHIR_NUM_MEMWIT, __TEMPLATE_WHIR_NUM_SETUP)
                }
                let count := __TEMPLATE_WHIR_PACK
                if gt(add(col, __TEMPLATE_WHIR_PACK), limit) { count := sub(limit, col) }
                mstore(add(mg, mul(32, g)), whir_fold_pack(add(mload(CIRCUIT_PTR), mul(16, col)), count, ex))
            }
            // draw WHIR batching (PoW fold: digest=keccak(seed||nonce_be8), top __TEMPLATE_WHIR_BATCH_POW_BITS
            // must be zero; nonce is the 8-byte BE word at the GKR stream cursor). Then draw.
            mstore(sp, seed)
            mstore(add(sp, 32), mload(ptr)) // the hash covers the leading 8-byte nonce
            seed := keccak256(sp, 40)
            if shr(sub(256, __TEMPLATE_WHIR_BATCH_POW_BITS), seed) {
            revert(0, 0) }
            mstore(sp, seed)
            seed := keccak256(sp, 32)
            mstore(sp, seed)
            let batching := mod(shr(128, seed), mload(P_PTR))
            // batched opening = Σ merged_i · batching^i
            // and the batching powers, which the WHIR half reuses as its gamma powers
            let opening := 0
            let bexp := 1
            for { let i := 0 } lt(i, add(__TEMPLATE_WHIR_MERGED_MW, __TEMPLATE_WHIR_SETUP_MERGED)) { i := add(i, 1) } {
                mstore(add(__TEMPLATE_WHIR_GAMMA_PTR, mul(32, i)), bexp)
                opening := addmod(opening, mulmod(mload(add(mg, mul(32, i))), bexp, mload(P_PTR)), mload(P_PTR))
                bexp := mulmod(bexp, batching, mload(P_PTR))
            }
            // Hand the WHIR start state over in memory (the __TEMPLATE_WHIR_* regions are the
            // WHIR half's, laid out by the generator). Layout mirrors what the WHIR half consumes.
            mstore(__TEMPLATE_WHIR_SEED_PTR, seed)
            mstore(__TEMPLATE_WHIR_REG_CLAIM, opening)
            // z = base_z(BASE_Z_COORDS) ++ packing coords, one 128-bit value per slot
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_BASE_Z_COORDS) { i := add(i, 1) } {
                mstore(add(__TEMPLATE_WHIR_Z_PTR, mul(i, 32)), mload(add(POINT_PTR(), mul(i, 32))))
            }
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_PACK_LOG2) { i := add(i, 1) } {
                mstore(add(__TEMPLATE_WHIR_Z_PTR, mul(add(__TEMPLATE_WHIR_BASE_Z_COORDS, i), 32)), mload(add(ex, mul(32, i))))
            }
        }

        // Revert unless equal.
        function sink2(a, b) { if iszero(eq(a, b)) { revert(0, 0) } }
        function draw1() -> r {
            let s := keccak256(__TEMPLATE_WHIR_SEED_PTR, 32)
            mstore(__TEMPLATE_WHIR_SEED_PTR, s)
            // draw1 reduces the high 128 bits with mod (matches prover from_u128_with_reduction).
            // Reduction is required: unreduced values break `sub(P, x)` for x > P.
            r := mod(shr(128, s), P)
        }
        // WhirGenConfig::derive obtains canonical base_domain_root and base_domain_root_inv via Proth120::to_u128;
        // powmod and exp_pow2 preserve reduction through mulmod. Binary exponentiation tests
        // bit 0 with and(e, 1), then shifts e right by 1.
        function powmod(base, e) -> res {
            res := 1
            for {} e { e := shr(1, e) } {
                if and(e, 1) { res := mulmod(res, base, P) }
                base := mulmod(base, base, P)
            }
        }
        function exp_pow2(x, k) -> res {
            res := x
            for { let i := 0 } lt(i, k) { i := add(i, 1) } { res := mulmod(res, res, P) }
        }
        // Two FE_BITS=123-bit fields occupy 246 bits; 10 = 256-246 aligns the pair.
        // Mask 7 and shift 3 give bit-in-byte and byte offset; shift 128 repacks two checked u128 lanes.
        function cd_fe_pair(cd, bit) -> w {
            let x := shr(sub(10, and(bit, 7)), calldataload(add(cd, shr(3, bit))))
            let a := and(shr(FE_BITS, x), FE_MASK)
            let b := and(x, FE_MASK)
            if or(iszero(lt(a, P)), iszero(lt(b, P))) { revert(0, 0) }
            w := or(shl(128, a), b)
        }
        // Round bits to bytes with (bits+7)>>3; mask 7 gives the low three padding bits.
        function run_end(cd, n) -> next_cd {
            let bits := mul(FE_BITS, n)
            next_cd := add(cd, shr(3, add(bits, 7)))
            // All cursor advances are profile-derived; the final cursor checks (REG_CD for the WHIR
            // stream, decode_calldata's end offset for the GKR section) reject overruns.
            let pad := and(sub(0, bits), 7)
            if pad {
                if and(byte(0, calldataload(sub(next_cd, 1))), sub(shl(pad, 1), 1)) { revert(0, 0) }
            }
        }
        function cd_digest(cp) -> d {
            d := and(calldataload(cp), __TEMPLATE_DIGEST_MASK)
        }
        // PoW preimage: seed32 || BE nonce8 = 40 bytes. 256 is the digest bit width.
        function verify_pow(cp, pow_bits) -> next_cd {
            // the 40-byte hash covers the seed and the word's leading 8-byte BE nonce; the rest of the
            // word stays behind, and every later absorb writes the bytes it hashes
            mstore(add(__TEMPLATE_WHIR_SEED_PTR, 32), calldataload(cp))
            let h := keccak256(__TEMPLATE_WHIR_SEED_PTR, 40)
            mstore(__TEMPLATE_WHIR_SEED_PTR, h)
            sink2(shr(sub(256, pow_bits), h), 0)
            next_cd := add(cp, 8)
        }
        // Draw `num_q` query indices exactly as the prover's `draw_query_bits`:
        // squeeze `padded` little-endian u32 words from the seed (8 words per
        // keccak block, re-hashing the seed before each block), DROP the first
        // word, then read `qib` bits per index LSB-first from the remaining
        // stream (BitSource + assemble_query_index). Indices land in QIDX_BUF.
        // u32 bit indices use shift 5 / mask 31; rounding to 32 bits adds 31.
        // A Keccak block contains eight 4-byte u32s; mask 7 rounds the padded draw to eight words.
        // Byte indices 0..3 and shifts 0/8/16/24 assemble each little-endian u32.
        function draw_queries(num_q, qib) {
            let num_bits := mul(num_q, qib)
            // num_required_words = next_multiple_of(num_bits, 32) / 32
            let nrw := shr(5, and(add(num_bits, 31), not(31)))
            // padded = next_multiple_of(nrw + 1, 8)
            let padded := and(add(add(nrw, 1), 7), not(7))
            let wi := 0
            for {} lt(wi, padded) {} {
                let d := keccak256(__TEMPLATE_WHIR_SEED_PTR, 32)
                mstore(__TEMPLATE_WHIR_SEED_PTR, d)
                // `padded` is a multiple of 8, so a block never runs past it
                for { let j := 0 } lt(j, 8) { j := add(j, 1) } {
                    let b := mul(j, 4)
                    // little-endian u32 from digest bytes [b, b+4)
                    let w := or(
                        or(byte(b, d), shl(8, byte(add(b, 1), d))),
                        or(shl(16, byte(add(b, 2), d)), shl(24, byte(add(b, 3), d))))
                    mstore(add(__TEMPLATE_WHIR_DRAW_BUF_PTR, mul(wi, 32)), w)
                    wi := add(wi, 1)
                }
            }
            // skip the first squeezed word => start at global bit 32
            for { let qq := 0 } lt(qq, num_q) { qq := add(qq, 1) } {
                let base_bit := add(32, mul(qq, qib))
                let idx := 0
                for { let k := 0 } lt(k, qib) { k := add(k, 1) } {
                    let gb := add(base_bit, k)
                    let word := mload(add(__TEMPLATE_WHIR_DRAW_BUF_PTR, mul(shr(5, gb), 32)))
                    idx := or(idx, shl(k, and(shr(and(gb, 31), word), 1)))
                }
                mstore(add(__TEMPLATE_WHIR_QIDX_BUF_PTR, mul(qq, 32)), idx)
            }
        }
        // Each deferred constraint uses 96 bytes: scalar at +0, running equality at +32, coefficient at +64.
        // eq(alpha,z) = (1-alpha) + (2*alpha-1)*z.
        function fold_accumulator(alpha, n, zi_off) {
            let one_minus_alpha := addmod(1, sub(P, alpha), P)
            let alpha_coeff := addmod(addmod(alpha, alpha, P), sub(P, 1), P)
            let zi := mload(add(__TEMPLATE_WHIR_Z_PTR, zi_off))
            let eqv := addmod(one_minus_alpha, mulmod(alpha_coeff, zi, P), P)
            mstore(__TEMPLATE_WHIR_ACC_PREF_PTR, mulmod(mload(__TEMPLATE_WHIR_ACC_PREF_PTR), eqv, P))
            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                let b := add(__TEMPLATE_WHIR_POW_PTR, mul(i, 96))
                let s := mload(b)
                eqv := addmod(one_minus_alpha, mulmod(alpha_coeff, s, P), P)
                mstore(add(b, 32), mulmod(mload(add(b, 32)), eqv, P))
                mstore(b, mulmod(s, s, P))
            }
        }
        // high_powers_offsets: bit-reversed powers of the order-2^fold generator's
        // inverse (matches the prover's `high_powers_offsets`). set_generator =
        // domain_generator_for_size(2^fold) = __TEMPLATE_WHIR_BASE_DOMAIN_ROOT^(2^(base_domain_log2 - fold)), and
        // qib = base_domain_log2 - fold, so set_gen_inv = __TEMPLATE_WHIR_BASE_DOMAIN_ROOT_INV^(2^qib) = exp_pow2(__TEMPLATE_WHIR_BASE_DOMAIN_ROOT_INV, qib).
        // hp[i] = set_gen_inv^i, then the length-2^(fold-1) array is bit-reversed.
        function compute_hpo(fold, qib) {
            let logc := sub(fold, 1)         // log2(count)
            // forge-lint: disable-next-line(incorrect-shift) — `shl(n, 1)` is `1 << n` (2^n), args are correct
            let count := shl(logc, 1)
            let sgi := exp_pow2(__TEMPLATE_WHIR_BASE_DOMAIN_ROOT_INV, qib) // order-2^fold generator inverse
            let pw := 1
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                // bit-reverse i over logc bits -> store hp[i] = sgi^i at position bitrev(i)
                let ri := 0
                for { let k := 0 } lt(k, logc) { k := add(k, 1) } {
                    ri := or(ri, shl(sub(sub(logc, 1), k), and(shr(k, i), 1)))
                }
                mstore(add(__TEMPLATE_WHIR_HPO_PTR, mul(ri, 32)), pw)
                pw := mulmod(pw, sgi, P)
            }
        }
        function fold_coset(fold, base_root_inv) -> folded {
            // forge-lint: disable-next-line(incorrect-shift) — `shl(n, 1)` is `1 << n` (2^n), args are correct
            let n := shl(fold, 1)
            let root_inv := base_root_inv
            for { let round := 0 } lt(round, fold) { round := add(round, 1) } {
                let half := shr(1, n)
                let ch := mload(add(__TEMPLATE_WHIR_FOLD_CH_PTR, mul(round, 32)))
                for { let i := 0 } lt(i, half) { i := add(i, 1) } {
                    // batch_oracle fills FBUF with addmod outputs; prior fold_coset iterations
                    // store mulmod outputs, so a and b are canonical.
                    let a := mload(add(__TEMPLATE_WHIR_FBUF_PTR, mul(mul(i, 2), 32)))
                    let b := mload(add(__TEMPLATE_WHIR_FBUF_PTR, mul(add(mul(i, 2), 1), 32)))
                    let t := mulmod(addmod(a, sub(P, b), P), ch, P)
                    let root := mulmod(root_inv, mload(add(__TEMPLATE_WHIR_HPO_PTR, mul(i, 32))), P)
                    t := mulmod(t, root, P)
                    t := addmod(addmod(t, a, P), b, P)
                    t := mulmod(t, W_HALF, P)
                    mstore(add(__TEMPLATE_WHIR_FBUF_PTR, mul(i, 32)), t)
                }
                root_inv := mulmod(root_inv, root_inv, P)
                n := half
            }
            folded := mload(__TEMPLATE_WHIR_FBUF_PTR)
        }
        // Plain multilinear fold (monomial tensor eval) with the fold challenges,
        // WITHOUT the coset base-root. Used for INTERMEDIATE/FINAL oracle leaves,
        // whose stored values fold as f = e0 + e1*ch per step (the prover's default
        // `eval_multilinear_with_monomial_tensor` path, no `evals_to_multilinear_coeffs`).
        // read_leaf checks initial lanes through cd_fe_pair; fold_multilinear writes addmod outputs.
        // Adjacent elements are the pair indices 2*i and 2*i+1.
        function fold_multilinear(fold) -> folded {
            // forge-lint: disable-next-line(incorrect-shift) — `shl(n, 1)` is `1 << n` (2^n), args are correct
            let n := shl(fold, 1)
            for { let round := 0 } lt(round, fold) { round := add(round, 1) } {
                let half := shr(1, n)
                let ch := mload(add(__TEMPLATE_WHIR_FOLD_CH_PTR, mul(round, 32)))
                for { let i := 0 } lt(i, half) { i := add(i, 1) } {
                    let a := mload(add(__TEMPLATE_WHIR_FBUF_PTR, mul(mul(i, 2), 32)))
                    let b := mload(add(__TEMPLATE_WHIR_FBUF_PTR, mul(add(mul(i, 2), 1), 32)))
                    mstore(add(__TEMPLATE_WHIR_FBUF_PTR, mul(i, 32)), addmod(a, mulmod(b, ch, P), P))
                }
                n := half
            }
            folded := mload(__TEMPLATE_WHIR_FBUF_PTR)
        }
        // Merkle path of depth levels, then match a cap entry. do_query/do_final compute
        // depth = query_index_bits - __TEMPLATE_WHIR_CAP_LOG2 (tree depth, not field reduction).
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
        // Each Merkle parent hashes two 32-byte child digests (64 bytes).
        function merkle_path(leaf_hash, depth, cap_ptr, cp, qidx, coset_bits) -> next_cd {
            // cap_ptr 0 = the setup frontier: the walk stops LEVEL bits below the root, not CAP_LOG2
            let top_bits := __TEMPLATE_WHIR_CAP_LOG2
            if iszero(cap_ptr) { top_bits := __TEMPLATE_FRONTIER_LEVEL }
            let qib := add(depth, top_bits)
            let internal_bits := sub(qib, coset_bits)
            let internal_index := shr(coset_bits, qidx)
            // forge-lint: disable-next-line(incorrect-shift) — `shl(n, 1)` is `1 << n` (2^n), args are correct
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
                    let sibling := cd_digest(cp)
                    cp := add(cp, __TEMPLATE_DIGEST_BYTES)
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
                    h := and(keccak256(0, 64), __TEMPLATE_DIGEST_MASK)
                }
                default {
                    // Bits above the path form the cap index.
                    cap_index := or(cap_index, shl(sub(pos, depth), bit))
                }
            }
            switch cap_ptr
            case 0 {
                // frontier[cap_index], after the embedded setup's leading STOP byte
                codecopy(0, add(mload(SETUP_CODE_OFFSET_PTR), add(__TEMPLATE_DATA_FRONTIER_OFFSET, mul(__TEMPLATE_DIGEST_BYTES, cap_index))), __TEMPLATE_DIGEST_BYTES)
                sink2(h, and(mload(0), __TEMPLATE_DIGEST_MASK))
            }
            default { sink2(h, mload(add(cap_ptr, mul(cap_index, 32)))) }
            next_cd := cp
        }
        // Each 246-bit pair contains two checked u128 lanes (cd_fe_pair); shifts by 128 unpack them.
        // The pair writes FBUF indices 2*wj and 2*wj+1; addmod produces canonical batched values.
        function batch_oracle(cp, cols, goff, vp, depth, cap_ptr, qidx, cb) -> next_cd {
            let wpc := shr(1, vp)
            let li := 0
            let bit := 0
            for { let c := 0 } lt(c, cols) { c := add(c, 1) } {
                let gamma := mload(add(__TEMPLATE_WHIR_GAMMA_PTR, mul(add(goff, c), 32)))
                for { let wj := 0 } lt(wj, wpc) { wj := add(wj, 1) } {
                    let w := cd_fe_pair(cp, bit)
                    bit := add(bit, 246)
                    mstore(add(__TEMPLATE_WHIR_LEAF_PTR, mul(li, 32)), w)
                    li := add(li, 1)
                    let s0 := add(__TEMPLATE_WHIR_FBUF_PTR, mul(mul(wj, 2), 32))
                    let s1 := add(__TEMPLATE_WHIR_FBUF_PTR, mul(add(mul(wj, 2), 1), 32))
                    mstore(s0, addmod(mload(s0), mulmod(gamma, shr(128, w), P), P))
                    mstore(s1, addmod(mload(s1), mulmod(gamma, and(w, MASK), P), P))
                }
            }
            cp := run_end(cp, mul(cols, vp))
            next_cd := merkle_path(and(keccak256(__TEMPLATE_WHIR_LEAF_PTR, mul(li, 32)), __TEMPLATE_DIGEST_MASK), depth, cap_ptr, cp, qidx, cb)
        }
        // Each 246-bit pair contains two checked u128 lanes (cd_fe_pair), stored at indices 2*i and 2*i+1.
        function read_leaf(cp, vp, depth, cap_ptr, qidx, cb) -> next_cd {
            let words := shr(1, vp)
            let bit := 0
            for { let i := 0 } lt(i, words) { i := add(i, 1) } {
                let w := cd_fe_pair(cp, bit)
                bit := add(bit, 246)
                mstore(add(__TEMPLATE_WHIR_LEAF_PTR, mul(i, 32)), w)
                mstore(add(__TEMPLATE_WHIR_FBUF_PTR, mul(mul(i, 2), 32)), shr(128, w))
                mstore(add(__TEMPLATE_WHIR_FBUF_PTR, mul(add(mul(i, 2), 1), 32)), and(w, MASK))
            }
            cp := run_end(cp, vp)
            next_cd := merkle_path(and(keccak256(__TEMPLATE_WHIR_LEAF_PTR, mul(words, 32)), __TEMPLATE_DIGEST_MASK), depth, cap_ptr, cp, qidx, cb)
        }
        // A deferred constraint is three EVM words (96 bytes): scalar, equality weight (initially 1), coefficient.
        function push_pow(current_scalar, coefficient) {
            let n := mload(__TEMPLATE_WHIR_REG_NUMPOW)
            let b := add(__TEMPLATE_WHIR_POW_PTR, mul(n, 96))
            mstore(b, current_scalar)
            mstore(add(b, 32), 1)
            mstore(add(b, 64), coefficient)
            mstore(__TEMPLATE_WHIR_REG_NUMPOW, add(n, 1))
        }
        function copy_cap(dst, src) {
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_CAP) { i := add(i, 1) } {
                mstore(add(dst, mul(i, 32)), mload(add(src, mul(i, 32))))
            }
        }

        function oracle_root(r) -> root {
            switch r
            case 0 { root := 0x048B6B79BA191BD30B0910E6758FBC8E }
            case 1 { root := 0x048B6B79BA191BD30B0910E6758FBC8E }
            case 2 { root := 0x048B6B79BA191BD30B0910E6758FBC8E }
            case 3 { root := 0x05F2F0518F231C5E26AA251C6E25027E }
            case 4 { root := 0x05AAEFB98DA2664FD6254856A869AD67 }
            default { root := 0x06510476F9662713D6B5172425CBA5B0 }
        }
        function do_query(r, fold, qib, vp, delin, cb, qq) {
            let cp := mload(__TEMPLATE_WHIR_REG_CD)
            let cur := mulmod(mload(__TEMPLATE_WHIR_REG_CURDELIN), delin, P)
            mstore(__TEMPLATE_WHIR_REG_CURDELIN, cur)
            let qidx := mload(add(__TEMPLATE_WHIR_QIDX_BUF_PTR, mul(qq, 32)))
            let depth := sub(qib, __TEMPLATE_WHIR_CAP_LOG2)

            switch r
            case 0 {
                // Round 0 queries the base oracles: the merged memory+witness columns (BCAP0),
                // then the setup columns, whose paths end at the embedded frontier nodes; all are
                // gamma-batched into the folding buffer.
                for { let j := 0 } lt(j, vp) { j := add(j, 1) } { mstore(add(__TEMPLATE_WHIR_FBUF_PTR, mul(j, 32)), 0) }
                cp := batch_oracle(cp, __TEMPLATE_WHIR_MERGED_MW, 0, vp, depth, __TEMPLATE_WHIR_BCAP0_PTR, qidx, cb)
                cp := batch_oracle(cp, __TEMPLATE_WHIR_SETUP_MERGED, __TEMPLATE_WHIR_MERGED_MW, vp, sub(depth, __TEMPLATE_FRONTIER_SKIP), 0, qidx, cb)
            }
            default {
                cp := read_leaf(cp, vp, depth, __TEMPLATE_WHIR_QCAP_PTR, qidx, cb)
            }
            mstore(__TEMPLATE_WHIR_REG_CD, cp)
            // round 0 queries a base oracle: its evaluations fold with the coset base-root.
            // Later rounds query intermediate oracles, whose coefficient leaves fold with the
            // plain monomial tensor.
            let folded
            switch r
            case 0 { folded := fold_coset(fold, powmod(__TEMPLATE_WHIR_BASE_DOMAIN_ROOT_INV, qidx)) }
            default { folded := fold_multilinear(fold) }
            push_pow(exp_pow2(powmod(oracle_root(r), qidx), fold), cur)
            mstore(__TEMPLATE_WHIR_REG_CC, addmod(mload(__TEMPLATE_WHIR_REG_CC), mulmod(folded, cur, P), P))
        }

        // OOD point PoW precedes its draw; the absorb is seed32 || one raw u128 value.
        function do_internal(r, fold, q, pow_bits, ood_pow_bits, qib, vp, cb) {
            let cp := mload(__TEMPLATE_WHIR_REG_CD)
            // read + absorb the next oracle's __TEMPLATE_WHIR_CAP (__TEMPLATE_WHIR_CAP*32 bytes)
            // keep BE digests for Merkle roots; absorb LE-word copies (commit_u32_with_seed)
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_CAP) { i := add(i, 1) } {
                let d := cd_digest(add(cp, mul(i, __TEMPLATE_DIGEST_BYTES)))
                mstore(add(__TEMPLATE_WHIR_NCAP_PTR, mul(i, 32)), d)
                mstore(add(__TEMPLATE_WHIR_SEED_PTR, add(32, mul(i, 32))), bswap32x8(d))
            }
            mstore(__TEMPLATE_WHIR_SEED_PTR, keccak256(__TEMPLATE_WHIR_SEED_PTR, add(32, mul(__TEMPLATE_WHIR_CAP, 32))))
            cp := add(cp, mul(__TEMPLATE_WHIR_CAP, __TEMPLATE_DIGEST_BYTES))
            if ood_pow_bits {
                cp := verify_pow(cp, ood_pow_bits)
            }
            let ood_point := draw1()
            let ood_value := shr(128, calldataload(cp))
            if iszero(lt(ood_value, P)) { revert(0, 0) }
            calldatacopy(add(__TEMPLATE_WHIR_SEED_PTR, 32), cp, 16)
            mstore(__TEMPLATE_WHIR_SEED_PTR, keccak256(__TEMPLATE_WHIR_SEED_PTR, 48))
            cp := add(cp, 16)
            cp := verify_pow(cp, pow_bits)
            // prover order: PoW -> draw query bits -> draw delinearization
            draw_queries(q, qib)
            let delin := draw1()
            mstore(__TEMPLATE_WHIR_REG_CD, cp)
            push_pow(ood_point, delin)
            mstore(__TEMPLATE_WHIR_REG_CC, mulmod(ood_value, delin, P))
            mstore(__TEMPLATE_WHIR_REG_CURDELIN, delin)
            // only the round-0 coset fold reads the high-power offsets
            if iszero(r) { compute_hpo(fold, qib) }
            for { let qq := 0 } lt(qq, q) { qq := add(qq, 1) } {
                do_query(r, fold, qib, vp, delin, cb, qq)
            }
            mstore(__TEMPLATE_WHIR_REG_CLAIM, addmod(mload(__TEMPLATE_WHIR_REG_CLAIM), mload(__TEMPLATE_WHIR_REG_CC), P))
            copy_cap(__TEMPLATE_WHIR_QCAP_PTR, __TEMPLATE_WHIR_NCAP_PTR) // this round's intermediate cap is next round's query cap
        }

        // 128 monomial coefficients, one 32-byte word each; highest coefficient at byte 4064.
        // Process blocks of 8 words (256 bytes), offsets 224/192/160/128/96/64/32/0;
        // stop at byte 224, then finish the 7 remaining low coefficients.
        function horner_128(x) -> ev {
            let ptr := add(__TEMPLATE_WHIR_MONO_PTR, 4064)
            let end := add(__TEMPLATE_WHIR_MONO_PTR, 224)
            ev := mload(ptr)
            for { } gt(ptr, end) { } {
                ptr := sub(ptr, 256)
                ev := addmod(mulmod(ev, x, P), mload(add(ptr, 224)), P)
                ev := addmod(mulmod(ev, x, P), mload(add(ptr, 192)), P)
                ev := addmod(mulmod(ev, x, P), mload(add(ptr, 160)), P)
                ev := addmod(mulmod(ev, x, P), mload(add(ptr, 128)), P)
                ev := addmod(mulmod(ev, x, P), mload(add(ptr, 96)), P)
                ev := addmod(mulmod(ev, x, P), mload(add(ptr, 64)), P)
                ev := addmod(mulmod(ev, x, P), mload(add(ptr, 32)), P)
                ev := addmod(mulmod(ev, x, P), mload(ptr), P)
            }
            ev := addmod(mulmod(ev, x, P), mload(add(__TEMPLATE_WHIR_MONO_PTR, 192)), P)
            ev := addmod(mulmod(ev, x, P), mload(add(__TEMPLATE_WHIR_MONO_PTR, 160)), P)
            ev := addmod(mulmod(ev, x, P), mload(add(__TEMPLATE_WHIR_MONO_PTR, 128)), P)
            ev := addmod(mulmod(ev, x, P), mload(add(__TEMPLATE_WHIR_MONO_PTR, 96)), P)
            ev := addmod(mulmod(ev, x, P), mload(add(__TEMPLATE_WHIR_MONO_PTR, 64)), P)
            ev := addmod(mulmod(ev, x, P), mload(add(__TEMPLATE_WHIR_MONO_PTR, 32)), P)
            ev := addmod(mulmod(ev, x, P), mload(__TEMPLATE_WHIR_MONO_PTR), P)
        }
        // Final monomial pairs occupy 246 bits and unpack into 128-bit lanes at indices 2*wj and 2*wj+1.
        // The final fold reads adjacent pairs 2*i/2*i+1; deferred constraints stride 96 with weights at +32/+64.
        function do_final(fold, q, pow_bits, qib, vp, zi_off, rfin, cb) {
            // forge-lint: disable-next-line(incorrect-shift) — `shl(n, 1)` is `1 << n` (2^n), args are correct
            let nmono := shl(rfin, 1)
            let cp := mload(__TEMPLATE_WHIR_REG_CD)
            // absorb via the large FEVAL scratch: 32 + nmono*16 bytes can exceed the SEED
            // region
            mstore(__TEMPLATE_WHIR_FEVAL_PTR, mload(__TEMPLATE_WHIR_SEED_PTR))
            {
            let bit := 0
            for { let wj := 0 } lt(wj, shr(1, nmono)) { wj := add(wj, 1) } {
                mstore(add(__TEMPLATE_WHIR_FEVAL_PTR, add(32, mul(wj, 32))), cd_fe_pair(cp, bit))
                bit := add(bit, 246)
            }
            }
            mstore(__TEMPLATE_WHIR_SEED_PTR, keccak256(__TEMPLATE_WHIR_FEVAL_PTR, add(32, mul(nmono, 16))))
            for { let wj := 0 } lt(wj, shr(1, nmono)) { wj := add(wj, 1) } {
                let w := mload(add(__TEMPLATE_WHIR_FEVAL_PTR, add(32, mul(wj, 32))))
                let hi := shr(128, w)
                let lo := and(w, MASK)
                mstore(add(__TEMPLATE_WHIR_MONO_PTR, mul(mul(wj, 2), 32)), hi)
                mstore(add(__TEMPLATE_WHIR_MONO_PTR, mul(add(mul(wj, 2), 1), 32)), lo)
            }
            cp := run_end(cp, nmono)
            cp := verify_pow(cp, pow_bits)
            draw_queries(q, qib)
            let depth := sub(qib, __TEMPLATE_WHIR_CAP_LOG2)

            for { let qq := 0 } lt(qq, q) { qq := add(qq, 1) } {
                let qidx := mload(add(__TEMPLATE_WHIR_QIDX_BUF_PTR, mul(qq, 32)))
                let base_root := powmod(0x06510476F9662713D6B5172425CBA5B0, qidx)
                cp := read_leaf(cp, vp, depth, __TEMPLATE_WHIR_QCAP_PTR, qidx, cb)
                // final round queries an intermediate oracle: its coefficient leaves fold
                // with the plain monomial tensor
                let folded := fold_multilinear(fold)
                let qp := exp_pow2(base_root, fold)
                sink2(horner_128(qp), folded)
            }
            mstore(__TEMPLATE_WHIR_REG_CD, cp)

            for { let i := 0 } lt(i, nmono) { i := add(i, 1) } {
                mstore(add(__TEMPLATE_WHIR_FEVAL_PTR, mul(i, 32)), mload(add(__TEMPLATE_WHIR_MONO_PTR, mul(i, 32))))
            }
            let active := nmono
            for { let level := 0 } lt(level, rfin) { level := add(level, 1) } {
                let half := shr(1, active)
                let zj := mload(add(__TEMPLATE_WHIR_Z_PTR, add(zi_off, mul(level, 32))))
                for { let i := 0 } lt(i, half) { i := add(i, 1) } {
                    let c0 := mload(add(__TEMPLATE_WHIR_FEVAL_PTR, mul(mul(i, 2), 32)))
                    let c1 := mload(add(__TEMPLATE_WHIR_FEVAL_PTR, mul(add(mul(i, 2), 1), 32)))
                    mstore(add(__TEMPLATE_WHIR_FEVAL_PTR, mul(i, 32)), addmod(c0, mulmod(c1, zj, P), P))
                }
                active := half
            }
            let expected := mulmod(mload(__TEMPLATE_WHIR_ACC_PREF_PTR), mload(__TEMPLATE_WHIR_FEVAL_PTR), P)
            let n := mload(__TEMPLATE_WHIR_REG_NUMPOW)
            for { let e := 0 } lt(e, n) { e := add(e, 1) } {
                let b := add(__TEMPLATE_WHIR_POW_PTR, mul(e, 96))
                let weight := mulmod(mload(add(b, 32)), mload(add(b, 64)), P)
                let ev := mulmod(horner_128(mload(b)), weight, P)
                expected := addmod(expected, ev, P)
            }
            sink2(expected, mload(__TEMPLATE_WHIR_REG_CLAIM))
        }

        // =================================================================== MAIN
        // The WHIR half's entry point, called by the merged verifier after the GKR half has
        // written the start state (seed / gamma powers / opening / z) and decode_calldata the
        // memory base cap into the regions above. `cd_start` = calldata offset of the WHIR proof
        // stream (right after the GKR stream's trailing 8-byte WHIR-batching PoW nonce). It runs
        // once, on fresh memory: REG_NUMPOW and REG_ZIOFF start at zero.
        // Each round encodes two fields (c0,c2) per sumcheck step, hence 2*fold fields and 246 bits per pair.
        // WHIR reconstructs c1 with addmod; seed32 || three u128 coefficients occupies 80 bytes (scratch +32/+64).
        // The high 128-bit lane is c0; c2 is the low lane. The round dispatch flag is 1 for an internal round.
        function whir_verify(cd_start) {
        // Base geometry (generated): rfin = final-poly log2.
        let rfin := __TEMPLATE_WHIR_RFIN

        mstore(__TEMPLATE_WHIR_ACC_PREF_PTR, 1)
        mstore(__TEMPLATE_WHIR_REG_CD, cd_start) // the WHIR proof stream starts right after the GKR stream

        for { let r := 0 } lt(r, __TEMPLATE_WHIR_NUM_ROUNDS) { r := add(r, 1) } {
            // `cb` = coset bits = log2(LDE factor) for this round's oracle tree.
            let fold, q, pow_bits, fold_pow_bits, ood_pow_bits, qib, vp, cb
            switch r
            // Round 0: fold 1 variables at 28 PoW bits; 22 queries at 31 PoW bits, OOD PoW 12; 31-bit indices, 2 values per leaf, 7 coset bits.
            case 0 { fold := 1 q := 22 pow_bits := 31 fold_pow_bits := 28 ood_pow_bits := 12 qib := 31 vp := 2 cb := 7 }
            // Round 1: fold 1 variables at 29 PoW bits; 19 queries at 29 PoW bits, OOD PoW 12; 31-bit indices, 2 values per leaf, 8 coset bits.
            case 1 { fold := 1 q := 19 pow_bits := 29 fold_pow_bits := 29 ood_pow_bits := 12 qib := 31 vp := 2 cb := 8 }
            // Round 2: fold 4 variables at 31 PoW bits; 17 queries at 28 PoW bits, OOD PoW 9; 28-bit indices, 16 values per leaf, 9 coset bits.
            case 2 { fold := 4 q := 17 pow_bits := 28 fold_pow_bits := 31 ood_pow_bits := 9 qib := 28 vp := 16 cb := 9 }
            // Round 3: fold 4 variables at 29 PoW bits; 15 queries at 29 PoW bits, OOD PoW 7; 25-bit indices, 16 values per leaf, 10 coset bits.
            case 3 { fold := 4 q := 15 pow_bits := 29 fold_pow_bits := 29 ood_pow_bits := 7 qib := 25 vp := 16 cb := 10 }
            // Round 4: fold 4 variables at 30 PoW bits; 12 queries at 31 PoW bits, OOD PoW 4; 23-bit indices, 16 values per leaf, 12 coset bits.
            case 4 { fold := 4 q := 12 pow_bits := 31 fold_pow_bits := 30 ood_pow_bits := 4 qib := 23 vp := 16 cb := 12 }
            // Round 5: fold 4 variables at 29 PoW bits; 11 queries at 31 PoW bits, OOD PoW 0; 20-bit indices, 16 values per leaf, 13 coset bits.
            default { fold := 4 q := 11 pow_bits := 31 fold_pow_bits := 29 ood_pow_bits := 0 qib := 20 vp := 16 cb := 13 }

            {
            let scbase := mload(__TEMPLATE_WHIR_REG_CD)
            mstore(__TEMPLATE_WHIR_REG_CD, run_end(scbase, mul(2, fold)))
            let bit := 0
            for { let s := 0 } lt(s, fold) { s := add(s, 1) } {
                let pair := cd_fe_pair(scbase, bit)
                bit := add(bit, 246)
                let c0 := shr(128, pair)
                let c2 := and(pair, MASK)
                // c1 is derived, so p(0) + p(1) = c0 + (c0 + c1 + c2) equals the claim by construction
                let c1 := addmod(mload(__TEMPLATE_WHIR_REG_CLAIM), sub(P, addmod(addmod(c0, c0, P), c2, P)), P)
                mstore(add(__TEMPLATE_WHIR_SEED_PTR, 32), or(shl(128, c0), c1))
                mstore(add(__TEMPLATE_WHIR_SEED_PTR, 64), shl(128, c2))
                mstore(__TEMPLATE_WHIR_SEED_PTR, keccak256(__TEMPLATE_WHIR_SEED_PTR, 80))
                if fold_pow_bits {
                    mstore(__TEMPLATE_WHIR_REG_CD, verify_pow(mload(__TEMPLATE_WHIR_REG_CD), fold_pow_bits))
                }
                let alpha := draw1()
                mstore(__TEMPLATE_WHIR_REG_CLAIM,
                    addmod(mulmod(addmod(mulmod(c2, alpha, P), c1, P), alpha, P), c0, P))
                mstore(add(__TEMPLATE_WHIR_FOLD_CH_PTR, mul(s, 32)), alpha)
                let zi_off := mload(__TEMPLATE_WHIR_REG_ZIOFF)
                fold_accumulator(alpha, mload(__TEMPLATE_WHIR_REG_NUMPOW), zi_off)
                mstore(__TEMPLATE_WHIR_REG_ZIOFF, add(zi_off, 32))
            }
            }

            switch lt(r, sub(__TEMPLATE_WHIR_NUM_ROUNDS, 1))
            case 1 { do_internal(r, fold, q, pow_bits, ood_pow_bits, qib, vp, cb) }
            default { do_final(fold, q, pow_bits, qib, vp, mload(__TEMPLATE_WHIR_REG_ZIOFF), rfin, cb) }
        }

        // Hardening: the proof stream must be fully consumed — the cursor (__TEMPLATE_WHIR_REG_CD) must land
        // EXACTLY at the end of calldata, with no trailing/unused bytes. The WHIR stream is the
        // tail of the merged calldata; its last item is the final round's query openings.
        if iszero(eq(mload(__TEMPLATE_WHIR_REG_CD), calldatasize())) { revert(0, 0) }
        }


        // SPILL OVERWRITE PREVENTION: 0x40 is Solidity's free-memory-pointer slot.
        if gt(mload(0x40), MINIMUM_FREE_HEAP_PTR) {
            revert(0, 0)
        }

        // Keep `alpha` inside this block so its stack slot is free before the tail.
        let ptr, output_evals_ptr
        {
            let alpha
            // the stream cursor is a memory address inside the decoded GKR image
            // decode_calldata builds the preimage, including the setup cap from code, before hashing it.
            decode_calldata()
            ptr := transcript_init(IMAGE_PTR())
            output_evals_ptr := ptr // base of the 10 GKR output columns (for the lookup-identity check)
            ptr := gkr_init(ptr)
            ptr, alpha := gkr_compress(ptr)
            ptr := gkr_circuit(ptr, alpha)
        }

        // Permutation identity: read-set product == write-set product (no inversions).
        check_permutation_identity(output_evals_ptr)

        // Lookup identities: every logup argument's rational sum Σ num/den over the boundary
        // evaluations must be zero (same as the CPU verifier's lookup-identity check).
        check_lookup_identities(output_evals_ptr)

        // The recursion chain hash (auxInput, registers x18..x25) is not checked here: the
        // registry compares it with the expected chain of the program it accepts.

        // ── GKR→WHIR handoff in memory, then the WHIR proximity check ─────────────────
        // emit_gkr_mark draws the packing coords + WHIR batching, merges the base-layer claims and
        // writes the WHIR start state into the __TEMPLATE_WHIR_* regions; whir_verify then
        // consumes the WHIR proof stream, which starts in the calldata right after the GKR
        // section, and requires its cursor to land exactly at the end of the calldata — so the
        // whole stream (GKR ‖ nonce ‖ WHIR) is checked for exact consumption.
        emit_gkr_mark(ptr)
        whir_verify(21971)

        // The verified statement, handed to Solidity: publicInput = registers x10..x17,
        // auxInput = x18..x25 (u32 LE each, concatenated, from the preimage).
        publicInput := mark_word(PUBLIC_INPUT_FIRST_REGISTER)
        auxInput := mark_word(AUX_INPUT_FIRST_REGISTER)
        }
        // Report to the generated registry address. The deployer checks its code before
        // deployment; a refused mark aborts the verification transaction.
        IVerificationRegistry(__TEMPLATE_REGISTRY).markVerified(publicInput, auxInput);
        return abi.encode(publicInput, auxInput);
    }
}

// Generated heap map (byte offsets; every region sized from the circuit / prover config):
//     2144 ..   2368  MEMORY_CHALLS (32 * 7 = 224 B)
//     2368 ..   2432  LOGUP_CHALLS (32 * 2 = 64 B)
//     2432 ..   3136  POINT (32 * 22 = 704 B)
//     3136 ..   4224  SEED (32 * 34 = 1088 B)
//     4224 ..   4256  BATCHING (32 = 32 B)
//     4256 ..   4576  CLAIMS (32 * 10 = 320 B)
//     4576 ..   4896  EQ (32 * 10 = 320 B)
//     4896 ..   6944  ABS (32 * 64 = 2048 B)
//     6944 ..   9312  CIRCUIT_CLAIMS (32 * 74 = 2368 B)
//     9312 ..  13152  GATEVAL (32 * 120 = 3840 B)
//    13152 ..  16512  QTABLE (32 * 105 = 3360 B)
//    16512 ..  30624  IMAGE (32 * 441 = 14112 B)
//    30624 ..  31680  WHIR_SEED_PTR (32 + 1024 = 1056 B)
//    31680 ..  32480  WHIR_Z_PTR (25 * 32 = 800 B)
//    32480 ..  41120  WHIR_POW_PTR (90 * 96 = 8640 B)
//    41120 ..  41152  WHIR_ACC_PREF_PTR (32 = 32 B)
//    41152 ..  41600  WHIR_GAMMA_PTR (14 * 32 = 448 B)
//    41600 ..  41728  WHIR_FOLD_CH_PTR (4 * 32 = 128 B)
//    41728 ..  41760  WHIR_HPO_PTR ((1 << 0) * 32 = 32 B)
//    41760 ..  42272  WHIR_FBUF_PTR ((1 << 4) * 32 = 512 B)
//    42272 ..  42656  WHIR_LEAF_PTR (12 * 32 = 384 B)
//    42656 ..  42688  WHIR_REG_CD (32 = 32 B)
//    42688 ..  42720  WHIR_REG_CLAIM (32 = 32 B)
//    42720 ..  42752  WHIR_REG_NUMPOW (32 = 32 B)
//    42752 ..  42784  WHIR_REG_ZIOFF (32 = 32 B)
//    42784 ..  42816  WHIR_REG_CC (32 = 32 B)
//    42816 ..  42848  WHIR_REG_CURDELIN (32 = 32 B)
//    42848 ..  43872  WHIR_BCAP0_PTR ((1 << 5) * 32 = 1024 B)
//    43872 ..  44896  WHIR_QCAP_PTR ((1 << 5) * 32 = 1024 B)
//    44896 ..  45920  WHIR_NCAP_PTR ((1 << 5) * 32 = 1024 B)
//    45920 ..  46624  WHIR_QIDX_BUF_PTR (22 * 32 = 704 B)
//    46624 ..  47392  WHIR_DRAW_BUF_PTR (24 * 32 = 768 B)
//    47392 ..  51488  WHIR_MONO_PTR ((1 << 7) * 32 = 4096 B)
//    51488 ..  55584  WHIR_FEVAL_PTR ((1 << 7) * 32 = 4096 B)
//   heap end: 55584

contract GkrWhirVerifier is GkrWhirVerifierCode {
    constructor() {
        // Runtime layout: Solidity code (including metadata) | setup data.
        bytes memory code = bytes.concat(type(GkrWhirVerifierCode).runtimeCode, hex"000b17eec1377487ccb1a57c72a4c0c2aaba3f30d6356ca8f5b8cc042dea9dedab602ad6b3f944dbfffc9bd9d5bd28bb04f8e6ded44a6bcfd7ff4cf2ae7bfc782bb413a1dca88900097e795f8773e5760b3273af1563cd1fe01ec5531da38877ab3512b107b5e240d1f2d016d5cde1b9ed8ba6a2488cefe04cf8b0474e89d6147aa055a2ca6cb47034a47e27a5488a3bcf6d18c2b31b3e4ec188a3a82a5f636c557eaa182eee65c6b66a32e8adbaf5b81bb274e74814a24e65699b4b42082b960b640d07acfc4f4390b1422f32e0df0a5bbface39de581389f3bdc2d53e560481b8391e5638a5c5e32931a602a22f50ee6736967c7f034f68e544d6fa64586a5b75a674e50d7de394ab41f505e55309bda4b0eeeb9cea7cec3563feee3525f643d8137ccaf9ad7de82866341720fca18a930e6beb3c10b17dafe870d94475f721e3b78b3f1f097fa19158dec90632b3ab5a03eb60a560771f75da154bc2e31a1a37d0ce4035d5fd3fc9a221f2f677234ed4d6ced7e232d8d41c6ee0d6c6c1c9498192509b8d386990f57879a8791a2ab818c8a09e9f03b9047eecc33b80fd4064e24a73da36142f29c821d80772cd6974d22ea1a1ce665c081ec0a7cb25e372762e79509b2e495832df66f4b8aadbec26f4c4fff77bcb194ce300f94c5d60de4948790b07205d75046fa84088635859b9d94072e4cc0c98ec7195cad76cd6b903fb9ec3f669bbede50b36e7f704dc29a2185cd7ae095af055f056715c072a4a0c176d671f59ae7fadd4f35649442efd0733307476cb308867f32367053efb9ead8e92f6b332a3346b2747afb0eccbbca05d0c7fda9cf31ecf0dc5c09ce6447891385a217adf2033f10f446b68318bc96f89bc5af249dd677d40df93710b44431a0df09e03addf7dffa648dec187f00159cf7a234d7db5d141b1f4a7af7f8c344c1d4f6bd7a7c124dac3e5668f01cea68c9db5fec3cbe4ef6a1fedaf5314ed566bea014f40f490d559cf327263513ad9dd9a817918515e55af39b68b83921cb49096bc8b60a0853597380149a2b2aea93d582d95ab0a024c4ed6e6182508769c9c5c91e1cb2122c8e9c9071646cada203901ac98575ae08b8d94edc96136d8653cca2ede76649616031ef0f9a6d4bf84f0d19729479ee3f2bcf121652d75e73d15d9956ce7b7a00f4142b816cb159322a7de7590031b4f2ffd8d660e921bae7229e6c463776ac38bc445e14d65b3b573bc9761019527862c805816349fa4411fd63f01d102aa0f21dc2956b7ab7737180ab0c46b7893890e307d922bcdf92d6cefaa2d46862ab816705e662f76ab6839fb5f3b65e7929028ff3786f0e5c31a0be156b780645c032fc502ee7ae56ee90205ae986b3e8cf3f03b7395a11a9fa9d8953b4c51a4e1d872ab28b269dcb7fda7fc2d99d11b13e50df6830ffd97252a99e01d039acfb4d573ff26685de87a457628816fade1a12eed3bef0bb2b2ac7720c173eeee116d5bcb637318012cdb0c819bdd8a1bbc5585719eb5dfd5a47e687e9b3e229392d7fd46d4f3d42bc73b8b1e9e74b1c0de1d717d89a08b664eaeff5ff324e548b73a2919bc1d6485fb486bd851f23324e3cc4b10501e814664e276f2cfa7ed7b6f38e3e72aa1316d28c7bfb7744fe0c84693de72d93222be51d984c57d49f7a211c6e7898ee51b9ba9043c6ecec3c69f53f55f9e1586773fc80bba226631d6ba0e75435c0083c1adf3e59e6ed34d420ddbb8102023c04e0fc1474445d486605afa8b4b66fb24105d202c77ae5c37a49d449e997001fb56e7da4d69335d56badcec7108de7578481e86163351764f062ad26d7ab698b0d4f5e83dad038bb9f9b6eb857feed3381ddfe4fe8fb236c06423fc36b71a7b448b83adfab5bb3cfa4857521b2503d829d940a05533e524d2fda8baf3eb43b675a1bab479bc96defd6562419fab2c2621715a2d60524632df193ab87cb61442e580490d521f309f10e892f9fea8a7c686892b47c21ca2afba34eb2ca35eae3a9616cf18b5d629adb856d3ad95c91b2aaf252090cb6f894beaac2aeb2aee51c6035a9f42782a52f159868725abe6b3ab3958e783ff3c50c85c9a5bd05b1c2db079cedac5c0726af594c15aac3539fdac5002078425ada1ef895298db11d6f82e20370c0cf0bda246b97db92c3f44322617f11ab5bec0834888aab161b757676fc7248fa75df2f0e04b0aa5e94bd726cb324bf6ac59c00018d7421f27f7bacb90a973163fdcc0184b53ec4ad507ae2ac706263ea6c0e8f20f6a58d6ddc666724d876ef7ea1e1b2c6692a26387d8d14656698758bfd5585c2e4b8eeaf4f9d55b6264da09dcc3ee045999b3c79088b8676be4758a9ed93dec30767415238483e40f1544658c914ea34881e9410e0ff737aff7eb48bd6d92f5d81f4dc559b7ea45098abb6b535758d3a1037b7b916a20839d533aeaf7b23ebc6c030134169187359c205ad189a335a4d8bb2cf8cc902c3985246cee2d4f8c389a754d69af274d33b28c32eca62327f8d4faa0d4818815e377e5e9f3b3afd3b1abf2d426deaf652141df2c1d6747240c31aae4139f3c38831274a888f41b67ce287adfdc10b58cd136886963718b470c7060846b82bb51dcd24983c509c03cb709c698f19c012a1f3202ddb60b692826797626aa959ca2c3c65c4c9459a41d254b65b4887c819738de9e8f7570623f8854999b9ff8034ccc99aed17b842b68c7cf24f1d136ae94923d6be2a0b7d7e11ab671a31f4cd980f773b7f73be0511c049e84ed9c6f4b5b506addb5bf42f24b92b9f19da6da5f1d862b0773b06e30bcbc5afe429785e6b048310209de66e702425a2cc931442402045e364fd0c072e05ec4ac03f9012c0e0a2a6ff8482e1a843987159a12266fd5740139606d2d776aadd3f074e43d40499a8515e270a0ac9444a50351598aeef3352c81465fb7c8f475251a0c7b1a72fc6c6d4eeb91ee64bc4b4f7ea1f948b3d8366b0db21fb570803791edb96c5e21e852bf2094f3810bf621b5f84683ce0a1a37d3c26e5ba4ae07bb356f2fd484a429c6f67de86f7b4ed7bf806223c294cf328d4aef5744252f4517c4f0351cfc2c583fbbcd9c1ccc6fd61654823d8329235167a8c7a2f5bd91ec1a56853ef741c99bcc359c502fbad60e3a1795a79dd6772707efc1dcdb8a6841dfbf872d2cfd888cee73ba74a8a5c75c8810ad7fe97b6752c3cec903ea5ec33efb92dc8bba7b592d0ee2abd77766cfb0bae76a1efbaf6670dbfdf4d20c427c5dc2cb4b50c5ad48483b228abfc2de6cad77c26284149da43a442cf6cf1ac3c3edf8364c2d2a445f33fce7664785b30a1952302fb9a26b91fe920e76bfab828a1abe022b236e98dbd17dd02ca083f287adc0582746d2bb6e4a4c404f9e11453dc8d0c7c0149690436520cc454b0291bff353e13757b0df384ae943717b0f3012942ad78b5942f874f706ff7c6b54f2a3b3ab8fca7c210c15fe2212a7fdeadb1bd63ca153f3d5cd310f81526ee6ded0560d899e48b508e26e8e5341658dbf5360e8a9b2718ccb858b8e3f674d5bf55630781891b741d4930f8be8b8b5530571d59d7a3d402bab464f2c0bf9555f2389688a604c01caa03c0a6c464a53b3ce70591a771e8662ba8289b88a9b9ada2f70b7a6eb0d291e9ea705628b6c7ff60219839b0fcba9f7c9d4174cf8f07c5af5e7ce8bdc5a76aca0bc2f5468541b0ed602481caab534040c3a4e83a128e81a63f33474671ff21ff95819e906b0cfd80752d8b42bdae507b3b2ba13081d9eecae23ed7eab5b19f38b942e8f01729ce39c21d2595fca495c3e8b7fe1797a0e2f4ca1421d706c303e39719f827884f83376fac98e20ec88e213e61d1ccaf371b5cd59cf171ca528b9579ac1c6809600fccb8bce4a18b430293b5070c0b2a51fbce073a93881c368917d06066a1ecdaeb57bc89890fd85b8955d45d96f3e941f46b6b63ae40be617f4e270071b36f3babbd12be41b08e10ad50413bbb77a0d315a806f7339f145b3c80796891c58c9fe96c8d9d74e9e39e116359be1454b5ed2d358d8f106722530db40d178210406f2592bc482c7cc00f1ab05d7b6be554d139186d2371fc341c5fbbe74c9dfd713c24aa9ac456c6d39188b8625c7328b9d47a114af791d3fefb256fb3b3889d2a274ac24a2d4cd90257dd3d0848557c629429e856938c69bfe83ae5004b817238eb46b62d2f53445695992cb849fd51b37b4f086f779ef53a4e3ddb8cd8ec2f945e72299683d9c2eda95ad4be1efb14221d75b265e0cd5efd4f99729f9d9fbf5b6f09a28bf2d8f036345e18b77972c4fc11889ebab856a0494546210bed9b635bfcb82a652ae1b64eaf3c87dd3685547d2790ae573c4510b985de6f909748f38a69e806ab4aae85d804cb33f27fdd345770d618e11dd2742fe5c58df1e99e81ed8b1676d3baa457a2e9f3c2ef50fb214c006d3853ba94882b099dea21863bf397f2b31eb519af50846b2dc31be87fb024a0051c2ce11f0ba99c3c8d7b7761257ef98b09324cbaa7d782dce9aae45e50cfcdb6a065eef46f96e4d7e5e782efa526a46eeb1490af66588d7028f59980c829a198ca03f4a518350d6782f522d32d21eb51ea705b9b0d3ba782ffca2f6d40232c1a3254a59af5d39035df12aef276e3a9ce74ebefe91ae5f88986af13ab44a1b6574cd64fb677552bb0b27641c6b19cd44c57adf5e7d5ef5cae9d01c64638a4a19d7d2e3b1e5960c557ac2e799f3bcc8de6e0b01e56883b295f2c80c980f9741993f5be2a6fe42d269bc0b3e6f1b920d1d57a52f68d1fd8be1f40af699dea34a4a5d1b8ae74b160ea0120c20f64f5ff59477d6773b0f620b97beca0784ce7970d2b3d85ba552be3da2524a74b0356ff8be81bf086856734a4135089c5bebaaad283955dc506df0c0e7c0894df8c20fa086f9d113356ceda49adf4fca423bfba6e272844cd91ca45264f6644a356b3725071894772afe7fda9f197792daa861e2cbcf1b693554abae9f39092323f72064915104cf84c41d026ea8856b1d239bacd46e0ab1818afdd2940de81aa57b5f58a6a7ce7006b26369f7c5897a1aec565bd9724e9e56cd5960a7000ffc26978d4c97c716054e316fb3cd46cbe75efe90c0ec567887f07714e63a519064f0e1a9ee482aeeb406234bdedc0130f332b7a7968433476cbe33b3639aee8c4330703a552d5c1a8fa091cb93d3711b1610d503ec335ab775bc5f9878a431b4c5b2b8b867a62432fe1ddb1b572cc873dcbdd4cbf5e8b4918b9e71ec95b64be1c4073c47ca5872ae0c4355244053c6b636428d27742f521e22553ba9af0da76370b41938d9bf16cf8fb4f1e13ce9aed91b3e365999594f79c612983da71584006d9a1130b2f97266fa6db92871e5e17cddef55148f5265ddd5730aa7fb871f262ec0efa574fff29d4b9d4017df1df5e65a9db57cece902b628c87bc9a101f991f122b78d94b17c6b350583e11873e9fb3eb49ca09e9d09db791496d4ef9479b557dad3ce4f45a81a35f53f9971a4d961cd5057e725911049e6171368ceb5e13eb1422fef9e652075d9fc1c07deb915be454b4bfa9881d41b0fa1264077e5c2f5faf4dcb405e48fdb58aa51e9f921b308bdb8012313a7ef4baf2235c9aea497eb343c641731f8aefa565b16e4f24c9b3ea083b496451d48d025658cec629455b7a5add84522a9ace86ff2c3d0f1e3c0e06e53ba90cd614b330fce8a754c905bede22b31d68bbffdf8a8db4cf0d355d0b446390a3bc368be8fd9221a8db70fd8ffe9a864c82b7aa669d37f5bdaebfe270e6a0a542c546286bfeece8a154bdcdd1799c6e580ae83400271e810b78419e75f4bf0e7b148064f37b2c0d4a460e4e2b7dc86fb2bb34ac49d9f710286f9f328641335eb31d6f08afb840ecae424090930c1dd484ca560f696400d882edf1b5b43fa1378dc712fbe1183f2fa531c70830ced81b8aa761dbc9d978182d130de3710e7941de688012a12493bd48d5bbc471a687913a1fa3a11f08e130b2932d798bed788f56d5a043bac3145e39b47ab8f626cca7923725974ad0ae74acd31e8ed0ad948a7b48d861a0765618c83d893638f35036b57f6a1c02ef532e7f5bafd8d915858254998e55f7aca73a9849b62c02939cc8f5ef3b2bd18d931e9d4981de40614202fcb3d068059b27f087e10e2b585e8d729014b43d328c0f675e70ddbec4960e7a790a878c9f5d6725462aac8accc16023edb9e8faf25e4c882d2d057fab75173706a04a828f2e5ef9b5e5142c55bf2dd0ab6116b2f3c7954fc134a493a003ade984b01006b1ee194461d9c250a5833375df9ea36a9163b1d525d14ea84c5c7e63e9100a0c1315bdf21c2cbc7f2dc680017481f20d064a8203623e99a41038fa5ee59e16cc60950f35ad10aa72e993d555480f4e1ae32dae1575f493bffa95224b2d7420ab950543ded7c14efafa942e96c216ec4b1899ee6afc17e9f3fad0026cfc15f33218cf4c9923025220dc3e877a21494711052c9d6f8433d03932c90be2d9a4ec525887c11237df4d48e4b6d6bf202197c0b6df91581bde7441c260d8fee68cab5a8684304f1edfd872985edc03ba00334685b0958fd47c686ecfb57ee5b8501975649b12fbfb8b6cdb3b1e980de1e88d58459cc11e41a83986460e5929becf901e7a9aaa9db2ee21c38fab6f15f451b33cc7170b68d50d7a3dbf7afaa665cabf8e76b8986b815049ef36dbebca823d997c351953d3fdc7cad097e29ca64ec3e89d85a57039844793169789199307f725fb0d4e6707dc4e6a8eafe127c82f10ddb52ff9cd049f2c9f003c1da54806f94e8b7669ec60f15d5a8175644f367f859856291ed5388263d61936e271143fad4db18b48e57b5abedeb9926f6c1d531146d3565efb322b0da47119f6ff1db8b40f85277fdb39bdd74e70c224dd6ccee3dc8a32d78ae88b7dda22a8189ef53a7f70c1b4a1a19393c762ae6a1473bd773ed461239e047e94d5333ce6ab652ee148e620fdb12999198c22a9e7bd6b8d27c276622e9dabd8b6bc6abb3655d62bf3b7a179a7c51c2f014e94b2805bcb2e0508a73b75632f30d5b168458a7140ad553d827801985ad49a8644f8b307af401b87aaee274d4aa2819a59e839d719eb50867a908900b8ba9f81d7d03ae06bc786efc3344e1ad4751897ba9e16393f9cfa917867219dd4f561a2fa925c1b810da4e65642f7635aff3a777866f61978852e70f5097b3cd3fdf9045adce89248f3864ba73979966c22fdb5fa64783de197ce7c85b0898985a12365d87388620da39c0c7fb8a0c008572dc3c2312a86db19e5bfb8ef33c7e6131df9793878211536e23021bf1edde0fe006c4fa80595400e506248eeb67c6ba30c8f25d25a257691bd996c450feda0e64f4345c57ff464ad54db0c20107655fc526ef269d00e8dbc5ecbebe13b9de8ab8f8ca75e6775ee66760f94192eebca94a5eaf816cdc335321d0381aec2cc3e17ee9a669e03f3837fd24eb3fdf891f44e9a10c5d97ac58a3cd0756e15074b87d7e17e2d6af05b53075c4ab1003418812f2b52478f2a7fb4bdd4fa034cc5416db67d68d04a897b9c2152b159fd9b03be6be871a1be4470a86f87d65bd8fcc23213df7c67e38acac4979c2936e028195879aa0b1e305a785a15837578d76eab7c9b5392695f45c0883e074b4f47307e06a43160e463b10269c4d41a319e80a3b07d24e84cba22bd2b2fcb0441e8be3fcbe22a38841be965f433abbb2ae1b91b800eccf19d36a063ba81318b58295dee6b52bcaa09e2cf89b9fa1a76291b96cc624bbc955ec376a49f1de5e8c398e9cc54784f5614a4be48b9919cd5878a9fdd9f3ea4828156786c3d0fafe350c78766d16ded65a8f3b0d3450fae9cea3f7d3ffc622a56a97fa6a5e8e8b769c2882132306ddf2f10986ade599328c64865da3d168084d7e04c25a0998dcbc4e0b7f61671b176ae9dddd160c48100a7f2d008d70f87cdf43fc69170160bc2f85448965e1cd74003171d5ef5a8f88150136250028a7de6f5ce2ff5b115a8723ee9f1dc383670ea46a9ef78ac6b819ce5cb9ed8b4f8d1f1f579649e469a85e35783df69b848a1bb0303792e63039e55b55f245b30b4cf923a25ff19bd974de7e4fc567c79b055fe519eab763ea8f13bb3889a255b91ee1035a24d44a4880337e8ee8f1d30e4e4ecf76fb11bc683ca865978d1c3db4cfa100e05d64f1dad72719bebf1299a6b05ff608cdd6ad32e8f72ae272ac2a0ebb476d92271e52513a63349fa54edc133f6b7d65e66667f54cdc224ab2db1b1b2fe4b2543c138509caa26ca01f5e876d29285b67cbd3ca3e7f194590c69b1cca0a020f93ad39b9777c70fe5ec3deecfdf3fb49bfa56cee2a2c50b6a4b3c26d27ee3e03a09f94887f3b7e7c7a6a83bc5906963f7a9e83a99a306b15bf922191324411ac620be7a72374720fc898d078c5cf743663a4596c101eb5c2546c8b27fd2ae758d33a47b246ac093b9a6c7bd96677cc50a48bc29b211a479c4f6f32f87053ff10ea69d0dddc5ba5cca894b0d3b519153c2e3108b0e42c0087673f28fc1a7cc926f5b926cb8a1fc81d80cf6d45999166d1397ab98664c21f0ec59e56e1087919aa4aefe770f38ea0fbdb48e9c3161a5fad4c81806d551a4df093304e51dd23d27e6461aecbf784a39a9f858cd4a1497ed2d7cede89a305f0cc65b5effdc00f4ef97f891503700415425de85c8c54c8ea56eb28680ed0635c4a7aac07df268fe79efe07f493e36d8dd6bbd18dfad6a1d890bed0873575424926ece68e5544119e47dd9f72a5f26944fec47b0a79e79fd2bf40ff4cb40ec8afbefa7d90d3f416cda20e8578945a474f943221576d247cb84c5e7d0780881cca37050b948493d0537088f8ce7d716356713f08aefb8d9094acbde183c98f22c626d19a5d9c7172aa5439c31a2d6e06c182a2e19e46fbcb3e460247333ade3f04c3a44d3925493ebf41c3749824e034ed062b7a23336c4dca41ebc3f0a4aee75d35751f9f08270b6958b977c519e9aad5e7c0996b4c7d772941f7d0855631b29c8550e2fb7a79d0fdc5e4f39df138c9b87a571a7d90624e0c99685f6ea23a8909569c499e9b6b7b542e789dca1f46a07f2eeeeaabc1e150006bba78944f9b3b981b68bd9008e788809dad787f5089a9331bac87e1f76a33c61b0575718e731c5e0a33963bdfc5a6e72b903393f4b0906a7ec52cf34b6f2dd5235e341921038ab11b4b35c5b7ded34608ac68ebebe174dfb72186f0315631b7bfa494c2272b84a84eadc152f20043bb06763198dd54606f39a689b3f0e8d32ce2524f09f9bd231f74fed5f14fbe007abf95bea684f556cf342c6ee59c92f509804f6024784a4b043297c91eeb29a2c8cc9cc2fe5827100cb10c1f773995b40bc24c99faba53359ba883feff0e6acc3d6e96da1931bb82ee0b6884420e29f2537cab52ee2d17dba92092a2368db4875924d4652c0c2ed40c92ced9532aedcb42066af825480ca0e7eed0f547895d535696279387b249e55538f0c583ba4cbc55939576243cb151d194a568acc96fdd07b83c6ad6387ba5eb414609c9bcd79d4573209b042a4c93caada7fc0d831980b46d9473d363b44d937a41427367d6989c760834ae28e3a1b0252c78ae8ad5e5b315a3302511f38bb6784deba2f07d34fa32f3051f87629b22215c10e50f320be26c727608336688c37d66f11959209c74f3314daedd856a89271c14f46b38c43b51bbb6e8213a3db7f2dbfdcaf95b7a1bd3429cafd28c8542ec119ce8fd3c2bd9b14aa337b03cbca7926400bf0b61ec439c173578567c00f092aa75cd84c193a6b7f96f1171ff1f9aa4f5a9fc6e7d0a1f0896162ddbf949a37a42f280e9c46d85e704b81e6bf03155767c85d016839dde2bfc552c6206ebeaab2d29a2ef442251621213f2807c5a2f4ba5d22124f38739bb9ef6987b92e9d586deac9885f1dfb1bac285587b855d2a2455b7ef7f304420d89d4ad04b6fa1ba235968b039df1f86d706090fb0d91df15c0b8f13c85f8d17bb59ee470979b2d3efe9f21b6b3d4d47d2f623eca615ac7b0ee4b3494f00e608fcca2a2933949c17ef7ae4d75f3ad3d735aee06ad83f1792a4bbe07d2c153e851ab793d185748e684455230a11895fe3dbd74bd96beb6919cfb19fefd64ed84ca843ae8bb1e6396d7db4a1e1c34bebd9d8f95e6a63cd95f8ff9c1a0f79c6d31a8c4094aa8b33eef76398543ea571020b584cb3237220639717b19e7795a836aa6f754314d2471766006a8394c88418be1e079b4868899ab5dad471fcc8fc11b7a1efe2574b0690094fa4614ea0717e16cd94308e2b8089a8fd6c9177b4c3d4303dfeea029483219b951eedcaf58a429b433e4ffb912ac4a9dca3f7cc24c0746be4e6a8929bbfe1e46f1a2247ee794e21f7e829786f919d35c323c8f900e8c56501d4cd63a99bc719b9ca2b563395da476f8fbe2ffe1532dbb31f7b72fab5a80ca1d39152ff65ae446b365afce053b89cec510311d55fedbe4f2c9cd9c66f83a89cb064cf2dc908385a7c61b873b243fe9f2f0078ab99ed941e1b8d6ad51467a36b50ba8c5d56c13a36ebe368b1f1f5fc9364e1fe02e1d37606c488cf9e284743cf69e6ab03b570eefd55d11fe3ccb35af47ff27369f3eebddd39be103b4b3f16d743e3d1b30769e13edd378d81723e048fa24180ba7174e39ef045d5a404f6097aee357a2c6ad75054179a842f4fc3ced697fe19beb6083da596e907b4fc6f7ed25c8d28257e5832fc50bebe7a49f1d64ccdbc7d94e2893463b6c16da4d73d83f1887ee5d33e53fa66517f2fc8a91081a56760e42934cc909c44df08842df0c74bd5db4de1776e0dc4df7840dd64eed30bf58972a9fc2a0108a736e55de8bd7b5d51b282f79b2b9b00372f46d6374d1bf8ad3fe59f238f8522d1c8ce64dcc054865bf52206990a5da31a57764e9b4fdf3e35f4320b2486415d42b0a8f927678a2c7764f044604967402c41ac52f55aeaf3a5c5b5037a23ae1227c064809ecac815fe018eaa9996bda69bea2ef6211a7426d838482cd56c41875e798a62e5a4243d5f029862feceed9f71348fb4c10ce47eceecb2a1e9bf728a8b413ba5d3ec2e4fd18720396dcde64e6df7f2ab083347f878a71c3fd9cfc077bf7430ec98cda1c83f932c2a15420032f1f2d95b7c6fb1456df05b7d2e5984c0e5f4ab7af1045af8cefdec1edf0ebf912839b4a4488acd6e9454b543363a05cd9b4ebd5f82ddffdefeec6417d3587db080845fc6c9bbc677eeb00ee3be1f76880558544b2189dbe3608170b2e1a3cc638cac65c2ceda480a8afcf72983b9dc9562b7f4b157fb133248fcf588b40db13edd3f44b31572fad1197b7e626ccede327e0c4f4e128328fe516b6b788cd11828046634f957d4ee9b9413461581117c05274674f56696459adbc9b2c3a43ce98b4f4398bea57f45d84e07a08fb27df8fb7a7b88933080ec75cc06c6beb0f31e3a2aa386f791270165d0cf191072e33cadb3b7dfa2bbf658cac889fa36ba41d8092003c3d202547483d2683e645816466017acd435040158615e5e572b19fc11d741826145249414a092016564f01c79451521ef41f7922f3fe8dc04da9eb2993fdde8328345f0d43fddcd56cc3fe837273694095b158cf15003ffcc23aaa5c07dc5551d8aa520aa7a89db14439c1327890100e32ab0c3582318b470a13807bcdafc60507609a93cd1743ec804f9cf496132c458b2dcbed2f9764e5d3f23c1ae6a4fa2e32b38068ca0587b8691bb76b37403399aadb067fe87fee7e619c0f6c23f0419f8806d907fe6f4be2476c3795167b14b1414d1591aafcf8401389b20ef65abf1ede2ed94568eb665665263d950fe619366fa42ec19711f462a003e28c608d01cab367b9892289f135c70b29a95c14c4cbe3e57f0aaf03ba4a6ec52301fca27478744d2979a50811bcfb1b64d41aa653f6d800b05cd3ccb4f2dd523c1dae03a1a0e11340ec70d7df05b3556107cd379a0a719974082408a8813c1afa55726b06baabcab4d3aa035a38707daf21065ed0527b820dc413d8ac320435160cfa853c95ccb07b1652360002d561c8493f1f1ef3b016937b22434f32687b6a3cbf6aafe9d35740a6c2c87af2a7fef5c386b2408f806663e2cac84b6b650560527c52dbed9123cff8b452d96cc589af4372f5404af6e001d4520f089e0b40e90c2722af56284cdb0db29ba2f14245b90a887d8ad434e9179f7a43304d76b557a32836681b4caa30c7a283a2ab794736d3bdcea7bd061536963dd40cbf49c155f1bfe434bd0f875534e11cb91007ea5dd1bf1817e3b8fb5aadb9f6c9b4add1edc5ecce214a5dfc5ddc02bf437ecd7542caf3de7e418529f61fc0975e7ff90bfcbd859c568eaaf92043b0d0e6b35c38397a9b0d284183434fe6e1209d2eb332d24f9007ba2d4c4c6b30ed56876dea849940ff68b1f802ff4326399646b925858abc48c7ca531469b04e3d0749cd133ddf4541cfa62b7eff8f4255d4af02d7673cfedf255a7935d297d342ef9e6d75d7afc9642268eafee81eed0e4f5c95d10fedf6946c01e75e0e3972c4b11a18200a3112303406811840a7a9c7ed1db2c542fe44ff12e9f712eb4b4ec721298fe61ebebe48c8ebf6f166736d923a5da2fc7106429bf1ac575613665b3f024b93481b683b75b88d7e9fefe05903745421097d316cf377a662b3bba316819c1b361d997466c7bb276f6b00c449c4b28e449e1ca70546c731ce4be0deb94daba24249c8189a687a8ae0f04ec3423e577b4ab00358866b69e8a6505ce2bfeac51e72bc08a50b53036fe639f1d860888bd6fcc352eac9e9b31784a1ad0795912996e83d991638a9f38e0fc5058b160c6f5cd5cf7643e7a675bfc25509c97443970e14cb2acef2851cbd6849f82f2b5a404cf100b5715166f3ede6ff2706f43cf4954572e6acd100c3de286574d96b8eaedce5d4bf1adceaa0a70b7f34c0fa70689429c3544d448117ac9b329501642626ae17f3e5c05b81d033d2887c35ebf6a2da500ff8ec41267c0018c6b2adf95f95e7482bc3aaf60b61d92cf04e2bfde1817888dec1ec6da891d437d55d8889e10e84b20e2bbdad1833dcf2a0827ee973a6a243e059f66baf875dbdba3d79f001f725091999a48ad5fd58541a9080e9f668ec513b8190972ca67e5ccd05b5d25eec34c115112e47c024a4a4d362a58b071ceefb34b49aeb0d0172358f7571d8926238363380ac8edf370ec7ceb6368425318eb0a82172640f9ade6d4f15c4c952dedb45ca0f74b14f9aa88a638d2a0eccafdbb25c9a7391afa9750bed5827bae4898cc5bc2dccb8b4d6ac7806a9475bf22401249bf7d259dd08a8af829be3f193167653bdfdae1eb6b2f856049030d3eefb6213c0167930f3943e56597fe30bc12f43db64f194f5a8156105c67ad9f6a2ee4346da92a7ccf29480afbbebc87613d1fd8603a34dae9649f85397096f0043a58f8f678cfcbf7bbb235be74d68084879f50ef534f54d25ccb3fa3efca7beeb9621fd193d4ce36d9c8015c671edd234cd9348d6b9ca875f01a3cd34d02d71d2b60098c1e46ab016f85c0070e59081228b47bec5ce9dc52a5025b21aa6e3f9f54663463239efd5ebcb459a9e738ec3552ac302f9361b2706d683e4307baedf3ca3885be4ac183bff38d901696e1623208add15f3fd54bf01d5d1b7c0fef446a37b8670b73816bc1855eaf36a5d62024a19eac2a24e0c33c93f92a4ff54b95f550a825124739fcbc186f90b3085cb879ee3172c7746d2a46d8307520f33c9593257388d630d195be8d9ceb5ac0fa3a2f4158c9fc7a4388f8e15ff0ff305d9e0e4ea1ccef18964eb2610409722bbb6cf6170cc32ee9d0d8d707a3d71328f4b07b284fb9dd19a78f4edd960278cb66e5d14c560dde75e276a6e6e7ee2aead23d4450fd68337cf774be5134a883bc2d1ae73d9502be8287e01cb12f13b6cdcd99d242d69fd338bb232c16d191f0283b07666987a4512b8250bbb56914eee24ee257476862cc7c0c0b574bf270e4fe0f0b7ba4540a825cb8ae5beb2aac9aef734074a366f3e1df4981a75830a0477a515fb3c0f8a13ee40403c454cd21010aff14cb9f279a48d9566431239c538052fa5c8ab24ff9e7530137acd0ed10d1bee061c43676e2f437b298024ca8123a3c487b56a047fefa4c4aeac0fde2fcce1d7555eba1d83b58cb1dcbbee54e9e300f01949935f408e3724bcd141a0db264e359384f067e437635bf3b223f67851beaa063148e32db174134c5a19d436f0e4fe150fa3a67d44222b3079b448d6c9ca5504b30a5f525b8c0bb6301bcdf1149e945c432d54e196ae25b44cab19119bd5cae3f1be091005b4ccae338172184a4af4f9364abcff0448676f13a7b3f04e74d40e0baa8df0fbcb57045ee1430c7cbdd74dad3de6f7ad4541fc07a2a3cd55125c145fec9bd6cbbff64ae5076ca8598b528db771aee9580809f0d571dde00f5c341263aeef86482bb23024483c778272b85912284f8ee4f0350d256e5901657183c5023c757699809d642fcb03e0a1d2d11ad96cae50e8c000cd0b80fe8a61428f10457d159361ea88c15b466d9132d14f4ce603cea050fd34725ce535ca6a56245b946429473f3a779ff573b368af61f2fe3d8a5fda8bb088ab4b37b872d6c90b2e07363026a22759ea05d45354eab7f7f8ef21262319db4f1bd1b635706d9b4453a7cd1b6d03a4fa82abc4d682c2ec3c7ce0079f66537793a8490e10b363ea95eceba2a5d3fcbc0c8057691fe6dcf4cd244a6e499c7f29561e028b2dbc46bc6d6888337d593435283dba42844852eb607db1b46213501f066b874272cc6ea084e1304e2fbfd9a89419670a6d09338e6a816b17c316e2fdda9ea35ab6d0b4d46c88e6dc26ef15008b84c68e2dba7f0489c83d1fec3fd743a31d949f9390eaf415bd414c39196b90cec4087d7ee6f521ca9169613ab028d8a5a30b5baf8af66f6a6cb69f10d3662a0a77af0c2d289b3c8b1da50cb49ff808a79c55c7db3d5271580194c5172244612e58a682198bb3a5732f3735fccf45cf030a477c42431cdc3d53fe04bccbb7c14f07781a46f95f71e466a677ceef41845edcd1535784e7e93494d3edeb8f2720e4bb22f012b1a8dff45d7eaa52e19cef9ba22c03c0930d5e1976b62a76199ed43d6cb0221e8e6215493dfcec897ae76b0a29ffd2f933a3398287d9ae0bd670756ebf937806d6d7a954cc408a5640392d08a25aa909861469e850261ab79d76608d4c9f998da0d05fabc7aa658a218ede68cfcd440c7e3c42c5612eb4c489e8be4ee9344af010a7407b7917cb3b6864777a3ce9db7402f70c71c3dbe72ca79bbcfec7da04f4764fc05d732a68ecab259d32989b4adb2391ba2e97e320633ae3b045e0fe692549393e258de915a4a75070289ee1149d74eb81b7bb5e44a22763b97a002328d70ae4598c55f4b39eaee483996537d02dd9701d281605dcb090df59de57c3603df1be7f13bcd17e27d8e19e7074b26cd25e05c64c57f627332334785afaf683733ea8ef40c354da879ae1aed4a84e18464ddfb3c3e55a8a8f99c4c22e3ab334bf6da10a4fbb655c781f9ca131e25c83b57fd1fbe2bcbfaf30c60ded7131a22928b6a19ad00c31906e41e36dea8e2778c9c6094d57400b9a5bd206dda91648c3592371607f67aecd85ec5aaafe7d7079748816e87c8f004319327a3be337e36ffd58ee6036a05cf4434f49ec08a6858eef0d551b2a40e501342024b9e5ef96aa30732a9d4f057ca5c8468e4165c94341ac177f6c1fd51922b04fe2fb2b735f67b083ded463aff3ed84450d8ef6a708f7a38ca3649aafaffc2365b9a07ec25baea264f188872fa5e8fe523090409cb6cf975ebc1d0281aa214598e6e9021a631aa50acba7a1fd9aec0a0ce5798e48b27f7e7c6d2e0915667cda6264c5f0ba35cf8c2d2ae9cc75d5b73e8b2aa2996badd0e5bd23df6783f162012d39fb83109db1c027edb0f644f647104e549abe15181a66ad4da25ef34f59b501ad0ca42cbfa60ff9ebcff05484bb6ccc3d0b08c625f824c7c2229b196409eea3bfc54a577ae551ade9eb7329916ebfeba076cf6377dd92159c86d37beae54f62b84f591b7c272558133ff2d5c4007bff4a6b18ffe2b07900ce2c0f43441e0ae58169d86b2f24324fe259fe4b53f137c80c8518ee6ce3366d2561e6ddd09e245645bff22cf46c15f3dd1c9ddb0ac8308d52dc28f57900760c9f421bdf341d07df7279c16e20e8f5768092578b9fed099270da6504797f39dd0016f5768ca0543e9d2b9eb978733f77059ae9b673b93fb882883ab437664d5bde113834bc910caaabb6ed97a4ca46bef58306564625e41ad526924ed01859b8297139787a8dbf45f2fd7f51dcb0a3b9583672556378d0d76ed7b9c8e1a7896416c9c8407c4db5498db68124a88a62cb583b2fbec1a26889272c0105891bd1fecadc7fdf210a50092de0e0c19bbfba45651b123960232d5e1a5191e3df3c6ac740643ffa2b121fb59962340e6f2a498a92505ece97f42dba6d2f30785c388aac1ab71d1107d9c4577090bda786ea752ca2a79eaf16b855189251646f12933dd3368c47b5ef13b9c7dc7a331db252754fba12b4670d55da3d1448cd754f68e868a8248ad82255f372cd25a6c087b95c00a94f1081cfe721fd2a258e1441935bc05ffe3815b4633b7fad891336f297c6630613bb5ae70be52e45214d554d9544bec9834b481bde880ca4947cf2e336bac3f23d0a81bf63bc9f4b5572c17280e3401db8767a622724f5dc2e550d4451f8b50584cc2254812055ac3fa6ac4743a52edd98ba78b4f430f9a03f3d009103a6f5f1dee2dbd4b64de25c0cfec45bdbb7619361ead4c9b61dbbdae4bc6bc995c2b1e7c06f21e4a5c607d826dc6418e4fab536416393af2b8573df03c49ffd547c65ae29611d977d7558bae50e8a20fab0c9bb5f960b0c2dfa5a0177a47c46ce4566fc300caa3074eb6b91cf7d1429961b9da3a55c4ebadc380d1ee04629a935a0b0a2420676a8cde9d1f13d63b374e2848f482b075a0cf20f1666d0093cdc02a32c9362cc429bbc3680145005320af2abfa9e071ce74fc3bf7faebdd5ecf5c63b8526a62d9ab3191e466f67f2033e55b21e1592392314941d7b20870ff335008a5f4a979bc314048e721e0f21923e07087318e2230611be224aed5513ab4925b36e2656a2d1692971bad288445015e1c41a61d9f5c3d451ec047e042623e58271a4fd3ac2b32df064ca9f43550f6ff8807dd4642e23ea8ccb37d18ff8e84179290224b911695b8a8762aa551e0b534e6c44cc3f4645e4a1846b669e7f37e960459e44ec416bdb107c77825713a2730985c67d014f166f84b0748e56d26422063cbae2e623c003d534a8bbabad13a688eb0842790b06258ce48f3858fb701cab74346c5ea728dd29b3ef04e9a7f676c46611de0ebd2681fe100db48ddcc537ab686f139b233d0fbbc37753195c046042e12d00069aca0d0bc838846a4da727b03d4ae808626faaaeef746a99d7285acf3f3f75a3dc3552b125082311b6c1a4dae1f2813ffe7975e8bd92d7220f44cfbd6203106007bbd9f48d718dfc915d806d563190be862c0c8acd21898b0070d088700a2284580bbbc985cb4fe6ece40b996afcbda5bb97f4ab3aaa956a7647c713506442054db26ed25130fab10c078deae98cdadadcc4759d9f94a6c3dd259ced14252a979da7611ac215e62d162f345f3b72b68e67be54d56a3865097e32c4b4617c21de48638a0d7abc9551df28c135554b3d367b2a64f3275e6510f6197af20ba4f7084e0d02e5a77a1e8048d83358b41dcd1edc716b1689a456d0b8e984851fcef19911841ada90c37373b7c4a050ad0be4deb4d24748d2f61cdde690e1b6cec920208899a33abc4178131a45ed0044003efcd631c0280407f581287f3031259345a2092a5eb714bf039de697310ed6dfe38812912aca4b755035cd03579650082c582329d331b72a1d441bb88b17587d79efe03d323864c5e0b580772701733e4d7750dd0a7c1383244b33d4e6d8662fae264ac0da6cbe59bde5c20f530319339b825a58bcba249e5d53fd1d9c46dd022322487d1a305e1f99dd72fd75e8fd0e4e3b19f8c9fc0a12609086f19c72c4f3520b010451f9cc7627e6d768c39f8029cbec0430b56effac1351a2df036ff1df8666f73b65a552c6c12aeb676eeb2aa99ac2c25b686198c70421b4efd105e66244b75af1068e4708de4fa0c9018eb9ad1e58d434f27da4b3081ff34fca195b08fb35a7f13e05a0452194514f5c3eccf8f501317f981d1f986db5c5a242602bab882d4d3cd758246079826e93eb8b50950eb2d293de64bfc71769f20ccbc7d43f3ba95c8e4ce517f9585136ffbbce8ba44e8396f33f6fb812efa7a90555dc0c07fc63172827379aca7600f08898a506f3702b225bcb8ef3ca89c039d03247d86af604c6bf3bd1c65b54a9a9cdbd6f1333a11d2f47ff20e518f0024c91fd71fbdfdde2068ae06af721b80a79a36708f6ae86689e1315c5dd374ec66987ef1890d003ebec146703e08463f050770ebd4b31f3c8a5ccb7b39ff912f9b45b014772009ed96e85d21fe68de228660022d71ddf4aa8e773325fecf410b1c3995e4110ed974ee3efbc0aea13ead07fb281d7c18c71a98559fa27ab6bc60bb66c2d57b7c4a9208be76780619e4e5ab8a5a5f87db3a1754d6510ae700d46f85397dd1d2af2f93e9bcad7a3021b71ccf142c22b2151ca10bfd39c18ce5002a97f76a2478e47071363611a2b565eaf4d1b25edcaa9904661c693b36a9d02283acb8c436e7d043525024224bdb55420d31cccefd8eeb8efdf17b26a9cd2f602e7441462244733b6e965c40e6991cb109e1859d0a8b67ac582dc204f8311e75cf7253ea1aadf4e90fc4540b4cc4dd460befc77f8ad552d347888477288fb1f91ddddbbe6f60e4fd1927eba126ad8c39196d9cd44d3027bdc5579fc3d4cedb1276067df8910ceddf799b6987a67560e44391e985280d7b4de090fed2c6b0f8e5d42611b5ed5a5db7a29d8200e0668b4ab9c01f2f7ad492fdfc98f0198b774129ce1c81e5cc66fbc3fa1bd3f5d866ae73f2e41658d45f06502ec1153c0ab6cfcb990ecabcf59dc3669d4402f99a96c44d82ef66779b1d91b4095db7a0d34ca3e2cd07648d3699b53e0dd616e36b7adabd5b80d92a9d693b59bdcb93df28e0cc855eb31b14f9abd618f41e1dfa95c41c978155c8cb83a83bdc9ca11d77693b5c3a2097c20fa20279262932a25647d79ef12880d2ab418df6dd1aba815fb2fbb79f303a70c6ac642b040cf5f8a1afca2ce5904a85eb146273ca140f7856bfc3600bd70bf15b414eecbd75dadf18221f623a146f9e4e93f3dcc3edcc549640baeabd4bc4eb647e04c04cd65a650aee9dc3386a507980765e053e83b496fc863d9a79f06d597c47561230daeaa9601cb0c5a98e23f5d21a938c1d98d5484b9d78ad45e982dcd0e4af5137d8fc2d637eb4396538e78b6c512879260651e8e52c917699b4ad4bb7b0d4128a88f1a6a2e8bb96a9f864c101e04d19d7c14b0b940086b78d80dba87d1e74583bd9642eabdc7398558f85d566fc546abda9ff89763ef35bc371706c313c45c92928e8773d52548b6d07c6f54707c88c39275e32f932008945d5f9bcea9ca679ebce05efc0bcd53b79f20249f65caf3234559f5808b5c0c495eb5564be729589987d2314892888a42885b46ef7a4187a79aa30fbcd7f691810fedc917307e5bdbaeddd42f97f09995da6b084b669a1fe726abd3dd9120cb87f9a9c916112bf5956cdcca2dafbfd59520ae68bb922593c071ba9dd129b7c9306c0db01a792855e7b04179fab66be0ba3773a476b7b8aed1e5755356fe302fa9bc88fc4ea72366c40a3a75241de148527bd89fdee76c2f6ffeb0b2957d3f90272f1824d9ae6cacfebe7a9d0df78aa9490715d8cb474f0e3ab94aab6526cf16f143e573016b133fdebc2ad901825a19e4bf615a6961979e138eadd3699f211410f84947f18c2dea365c760f02b2482221af9c901464b27a71810b00fde5ea8d1ad348c86884f84f0d92921ed8162fafaeb20364da1f93d106a8130430ebe9e62bb4d24f1bd4a9df0f71d961e13fc09647d5b4808c6515bc4b2c9d19e338f5027ee2929395a76485a78ea90e7692a07302049b650e7c10435067bed455051c767a0808e02d8a738998a0a85968cee9164ca3d7da55a027205880103333c4e35fa229f0124b79f5c47d2394880f53e7847a5452671be0bc986ae51867cda5af8ddf6e0d15f8492b7cd6fa1d1aeafb6333f3ec3b5e2fa6860439ceb0f959b950a7971c5633658a1d3503558b3168cf3ff51483f822b19dae9455f9e86a110fca636075ac415bd42fffe774b87cd365bf19f07df682ebb3fcf42e82a63c690807416ffb73c9ea69a270766e00b98327a4d0eb70231382e05cf0631ec1a896bb9abae64ec6b670b289ddbc86eb37e998aebfc3ed9808d19687bc3c9d63262f631e8dfedc2cae87d030eab6105dc99a5acda92661fdc7c02a472e5db5b69adf407110535c30af219c47027c5af06a38d6138f3babdb7d017d486f1ede70a8ef0465900569115a1b545e30ea081c2a157b55e207a4721746b8551c26e6ca522d88e43998cc12b396c2baa6cb5dc0148e3b42721d674a87aa1f082b95bb2d0c19bc510c51068ffaaa05812f80034baa236d6ffafc8efb2a520f1aca602e2cc730875b2eb61b90442da69d2147fecfaa70248544d51b82b525f2ae0c05d31aa4db3705be08f96e872cbe64981563332ffed38b0c15d3f9490cb7b26b99d20dfddfee14353c2974fddaaa195ab88af0e84ba53f67439d1b836ec74cd7c4b0b41e3ecce9456e236ec1c1645b18cd271839afdca651c2b6cb80371e66e25c5a007ba5b78a2ff78f2c7cc31cf7a128efb0cc8083f5b456062f248aecd5af117b140bffd478ebf2360bf84ac86b5acf03b460b69eac991417eb03c5dc46f3b5bfe2fc1c5dab6b5ea29e9b9e457d97129186d44a7848a7709959287216f6f6fa8a243f5572e1c30723d594da9cdd68cc12d7f44cd0fbb34fbd0de69f985cf95b29f90ccbf412d658c2fc5d42f221ebf692ebfee3a4175fa3bc92edc28ef8c2a6b3273a0cad83f61fd98c573fa604c1f4d98bbf6fa61fe38f2380867cf486251987b437a6f3c8784d03fa3012165a4b85bd1e1dc55c8f5c8530c4ca446454e84a12a909f0013cb441ee23aeddf40cd9743b1bf8ac23542029642d8371bbf17861676eaae85a6fc323bce6aa4dfed1c09c8e1fe45937192680fef488ff0e71bfb413364668112e6df173753c9e9ad69f08768fb9697f7a32d281bd4dca049b3da2b8141f1f5ed21b5e6e74ff7b9d39b9285c97316fe0ef9670fa9aa12084ea58bcd739d5bf24d5f15f2a9748c9331f5bc308e8bf7076ea22637685e29e20595c1a46249eb8d7a2cc56e72d4190972107e142f3fc552ad4dbe85987633e8eed7127022fba5ccd1bb3313becdc9271123089807e335acffc2f7a7caf6cba67d09fd2fd9920984f9e35f9e9ec53d3be206280127bbc62c4e8769364bdb3b647b380ca58e47cd4c12162d330a5dcb238decce7b53acf0c0c8ede03604e73edf847c49146d570e14cb0061aa6b7915581bd425fa5c21698051b6503c842212170bb7202cf29d310d093fae7ebb43392a40655baf61e67986784ad3bdb392d3184c1c2f86b0c96abf450f6580da56a403f0e9999af53f80f0775ab1a1bf2f86d63429cfbef4a42d1fa7c23a196f686013a60eacab0729241d8fda38ef24a5b372b0d3f38d0451b1551990b1290ba1432273fda26e054a23530a677007ddbd08a8e8207e69b9b79024698dd316f2d58148cfa6e3fa1743f8714652aac5a452b603dd2b01b8e8564e0b63127e6eae22345f9fbe8635fed8c0a3d4ec4ccb7230fb9073978c9ad44aa206d9e66de38bb9715c0f29e672cf3fe59fb8032877d64bec156a5db96bd90a33262bc9f6198125a3448aa877e96974adc9bad6fc7bd566cbf1b3520f25f4aa3192661b980967a49ecc32513eb331994000af42b291b6b6f1009262243e7933968166919e5bffa0b8b5b556229520479312140f4a75858bb6775e48dcb48db3244933720d9cf929b951a5ea83aa830e4b0c1283814adbd8b188f9ccd4a138b080a15f80c55bee3cb2773f2d4a35f355a69fea931c57a5919ff55bf496d3adf2dd23cf0d1197bc2555b805320b8f3cec456fc4abd3191c592e31a4a51040c3058d398526b3197fed733a926e705487c04e1c4e8af5f64fa747fef00e674413dcf679c405720e2391a9560943a1447d13e6c80dee1f60a674f01b5ed647759185a20f1ec73acd7844aef1e4c0c1f598bbce5d237d432e53706615055ffeb7d3f1f13f4321880a6c7ffec5fdd28809e4aa22d442cd8fc461d9c6aeba18d9f0329130a33dcdcb200255bc329e0956c4bf8fdfeabb1169098b755ef1ef0bfafe2724aa93e135878119d6b9bac3029efa659a04ee407f42c12377a842ec2adf2925bad95d984aad700985d1234b2d741336ebfed9e47a3532a4c7f19cb3b0e3fad460a77551abc0a06634ef599cfffa8a4f01b210d669d7ce8729986414e60f5b2d8ffb9ab229663cebb6ec0cd798c3b599f18776218f01cbb9144d99d36ec74c5bb9db6892d772c43590e63c26daebbed9487c6c7042af0aec28544795359f4705536cbe720a2b6d203b6dff5572f5178db03bee31775d85c1bb3a77d60fb7dc6126cce7011d2302d3a96a20f2b999fdf3ae2f01370b4eb825bbe0f4a7f173ec09c875b5e2b63967ad629962c97fec14344f1e1db758df955a8ca80e68168b4a6a46b1a9338e7564454f22bf89499a9309815c5c47bbf907ea7f1228262ccd8fc5e023e2a96dcba140c2e6b57b0b13291bd9f0444b20422563c4364684deb2eb144fa182fc2ef05a17617349452a8f2505ea8bcd3d590c3a0c95f7047c3444b2d20a0c2976561dd95a583f52a873f460fe717175f4dc5fed8710ed2603ff57143d3718a74d810733c79fe0898d85f8dc070b016944cd217a3bbffed21b8715379239f20fbf7088e586e46c5d6726be914642f6a631db9212a4c354b5d81ae67b4f5f95a465824f0d95609e79da3ed390576bd58c0800ad110c05ab7051462a2204e102848e672919579f899e72e82293f5c8815433bb93c251badb29e7925ffe7fcc4c825f2b839cb93c63291ef7d574ffb69d9830a0db69637e926f075c79f7c42bb6a142a0ba77ef3b7aae60f540d364e0b46e785e3c5500ec2b222b5728dd3a018a3b1adea2c4f733b1bed78dabe4eba25af10fdc25df0cd8a6fd66fcc9a5221b115f04e0ac89f0c93fffb05f495c61205a6c95d1c49fcdbd18032566c09c8dc814ee32c68b5539b6d455a977db848b2fbb6fedf59e9daa19186ee393b80479f77adf7ef118a43756114776ec29655f52a302f3aeb7f3947cc986178b634cead72dae7ac543b9e0e2544cec0f5f7b02337e0998387147aedabdc63eab3d9dcb239a7bee64aa82d24e3944ec467af7036a178dec2614eccaddfb9537cb31c13e290ab248999b540cb5a7372b2d6a269fc86d7ecb70bbf9fac41e6fbeca01de537ae05e09f1575c97b29d07d08544bd73a956033769f494861a3d52b04288f2176498b2989344e826cb3370802246c2767026da6f828d57eaa66db98d730a0035f138cec30bb08b5ca68500a0fb3af6b1ef63f09d63c29f15c3039a92f63a9130538e295a3c424cce9ace4f8077d228854e102ec5b08d4d50c32c1d2c2068c56669f96c1f82f337489e08973c1506f6442239f4b4f90a79e13f3d6d1afb56448bd4b78d75a15098d877c11654e1d403924cf49157307fe4f64d7c902d50560325f2736c6acb3de896af31778815ca3d967f9831b32d839ad1a17acfb1cde069ca93c5490c23dcbb74bbbdf0ecbffb3cbb5db1700b04723729c96196c9c5e6d15e9474da057c11f40c0a74c910cc1b040b37238fcec6c2c644e669573f0cfb64595e7a54cd068ea5f1b81488877e0d3203e1814d0942d1fccbca0a2feb32c4698830ea1aa29e51e8619a5a78ca0421d09d01dfc810dd1231aed67f8e9560dfe1b965851843bbaa9cbd82c5e4a43b20e42ada0b5b0ebf911c709a1094a144a0d55a5af1fb0747391f423ac274873c82647c8aa19f4d713f7196dd6f3388776d53d49025f85afa72589a69b884322cb2490fbf910567ba0a942c82648da4dd807edcdb6853929928a3d20d1cce90fbec758a17e55e10ad614f41268940cde642440a017fff8c2de1efb412787c75de292628338d874b57bb6f8df91216156b019d9b5919514e33d36d72f65cc7e91a044ce657fc369660bf815dab7acf6c883dac1685d600bc7a29d30166011b3bf0d26c17a4fa2c10e7354b19671010acd52f3ccfa5a1c17a0e664753724ac80e1f580745a66d5861f2c7bd2ae6cf0ac9e797e63de9789b172a4209e3bbbdef0b5775511b4c35a398de52eb96f8e838f0a027bb897933bbd70d9a3e1379e33bf5b6d83ad95653bec3786e646e763013fd8a00354ddc6273e35e43a1f02ce7f733813f89a8b474bb1e7ccb9cd5eb22e955d26b55a9305b25c8c5f95149a91ff3a558fe835f34a1a5bb4834c9e145e20924932d3737a96abfcec3d51de302c78790c1194c2eb26ffb387dc9728a823ba179a6ef1c632916dbd522a74803d6e45ec0ceb78f85207b0ec78fce734809080d234820118a9712384a219ca0fa2e3c930f91bfa327d2c21cf9445887552591294b4b6562b0ba656093fbeabdbdfe198a0e3f53fde8fd114517fb0571a271e8eb55385bd3e675c2c61d50601820517de761a26a9942c60c0b579daf1d0c614d1f4f75af8df5bf9f5cfc2792ea70abea62b4a4709fd51aa3de0613ee4d7b3e27a7162abad65246f3f0fdbb4500f07d3dcc07bf5db827dc0b6c5d2a5a3ec819d91331be5ca9ff4d72a7cc523ff670446089662a288da791c3869d6f1ad337e44d4077331dbef7f5d75c59565b6eec11f6696d1322d628d29cefa0be1e2767d9b00652fed367b2da735d8df69b773e77992787cb656060ccdafede4b0a391186f81f23a9761defdc94af4ca57fd8a4b9f66dbb44d1ee7b1107274b5df883c2d462ee2e56e59c35a19f6519c2ebcd2e6604e15f08227a900b4e30ca209459b96012d5ff52d30089a7c3a7ff1e52ee48cf72e853420b78dcd8bdfabd396db2f774062f41500d9487f2be5d63702e661ddaadb947547f75c8c32a6d96c8ded478f371a9ec4ca03893c235142eb126cd396d9fb9b93f6f1c75d5da67a5cae58dbc32dbfad9c1d381f3b03de3c8f13a76ddff871aef411414871c9fcaf70a0325e332ef0b4c1165378d738de5892f454f92d73c500590775ef8f6522c78226f1e7d180ec11782d12af43bd266bbce415dc7783bb0ce91187878316ff19ef993f736fddaca68840737954ee6de37fb90ea2c1e1ec174ad6c2aaf06250c1d71ae6050ebf14e482703b9017862d942b6502cd5ddebe1899b5cca7ad5db4098f86f22b3cb5369f4cf7e85d2d5e72deb20a9e4691a7c712f5dc40d612a0e6406437af733b50f9f4af0d01fe1ed0b95b4a37f64a00ff28261da306c3ddbc9f1cad67da31786c66bfd291f255f064aba328c244b760d6f47edc2bcf0049717cbb1b9043442e74a65d590632637d1e4c6eb534ecb4817e61c29a5d091d73106b07fadecafc8abf20e8f62b5e39adcc2cf1702b180aa4ebfbd806974de52ed02f2c918ae42b47ba00151fd5fd1e9ca61816fc26dde238b2cebc81b1984df52cd0f267c327ffb8a8eb2b8d9088b8be6ec87c2a46d826a94f9a24fb6ecc0ff07641718d13690a610ec6174160b39a8c5eae7fa603c295a2b779163d9fd21b3fa1ead3002be72e74b22fc5a64d83c991fbfcb65ac269ed1d1981b4635dd637bba2fb909cb0530e731e75bd79daa8ef7a8777464971cc1b968f6117df3969555f17d3c8071fe71e7058ccf20400c8691777f36ca2e2dd2f1211c281907d1caa63ee2c22b01cbe04e33444d9acc8c02018cd0fc2c70b836ae4fa34682026d14d8cf4d7b386ba6477cb48ece6eb4a78345d4c6d3d84672645330f2818443a3292230a6f47a35ead09c9e2cca7e0850047a960b250cfa54f286364474bf9d1e3b09562ae52bd7b0230af27c92972f4bace8dc5ead6894a3d4c999c2074283a6e0a7adf90b9862c1e8096be967605a97eb76877859ec6b89168ad78af63f7c1bb977e90b89fd2b75e7f1eb51750b367d0a9e88dd150953dc767a5696d5c6f8d73b8febdb5334790c702bfc30529691c021a12bedaf136110782fd1f7bd52f9426bb42467cf50987e1611c8c5e2b4bf30f7b85f4fb6d864dfb031d83de9a11cb896c3db4c7cc776c56da0edfa03b961031e369f9210ec73acf382a331cb53918b79d956961b7adc402eb61fcc78109f23d20ecc285ae6e7fdd793c97413dd8837233ed13e4a7fb3b34871b2054e2587cd952f718105de721d185d53611bf7551e6acbd7f2ac00558656cfcb1809da573f6f1f00f86a18372e7991307cad53e98517c765df1d8ef49e0436673bb48c56b5e2ae0c6f2b1eba2a7bfbc9f40880ae6c49038508f80ad1e7822106fc9544758a7e2aff7b677e53e225f226e5076c2488391a46fb3773f8eab938c35373069f332cd84879d69b9e86f097122ed71f6a9edf60310ee70a4fa232a23ffefc4d42a6f7d4e24d94341ec79095f7bd86b6878068d9ef8636c235ff6951fa5c92232f67935ad41416db40116eb2a4777f44efb9f91815874e9fb5955abfd54915f74a960461ae25f57dfeacb394c32b93b8db09759b977caba40ca7775f17cafe4589780b33ebf94b5e6d8fd7b69e573868386e13f10d9debe43ae6b280260342794e4883eab4a2afdf6d5a80919135c53a72207528c5421cb1d2a15aa658aac731252110e6b594f9e321a696e69d223df313589c3d610d905811394dee3cb7e511a18d33b326f6afb3203424bc28f57eeffb5198ab578f2f32b0877b656d3a5ba9019f1acd5257317ecb21ed9de30604d106f808a9b45b0c1bb2b295029763e1473b0e315a63dc00600adec5126145bd932febd54d47406152af8f5103d53b03bdf4bf6d314a86d66ba6916dc83ec634638c0aaa6b86320aada28624077ceae2bf78b8e3d5428489e888d641658b2e962c19b402e18bb2dca0c5c22a0d5ba0902aacb9e46b02d03005ee7c30863e495aa2ff9e743d44b401150dd6d81f2eb193e5d5e4b98cb2f7d0db129729003d3cfab158221861f418701fcb31576426ee4b6e054ab4c50ad9226e3f2f3c454a1c0672e543ab6114b747dd87da55c35404d7b157f3e8d991b09ae423b6d1b03bb502ea298adae1564d5bd38716d9ab208d114b4afa56aff45cd72eb013122481d568bd2ae5b400c27649d02d483c62ef1923388dbf9db50688827b4f5425d8c82cfbd192e2c980cf845e9396c29b6a72c8a77e220171b24cb49d9f6af048a0a506312ab9fb7ad7b48205c9dbc5d6fe24c7cea0896e4d82b26292c4b5cc4f64d6d1e2c02a53a238f643480447fdb92d934598e91c4e98eb05f65907e1e17e069493155d036f40fd68a2938bf6aba0056fecf3d130e2e7fcac22a9b7e5049d7b65ca5973ae6ec4a5bcb1dcce0257e932f4b239ff957c45b27d5769425682d34937a66ebe3b4ba0e2a47f258dca42c22888da586fba16be202f5718860400f6d7960cc6323b0f4d042f6cd86665ad993bf60c2ce9cc913ab7c1d625128223bf8f6a6676aa31d75609b1b98c44e11e81b54d5ee8116ef09b6c54868f668076fc8f6da542084b0b0f8640ca1cc5fcfe3acb7029c295f24db05d607467785e58021c28f5d066d9d4cd662fac53a940adb152063df3f0015609c392bafc26cf524d829ce55a3c81ccdd4040007a1efee67161a3684b7e36a7744fb66430c9c79cbe488b8c247c04ccf833a30395d8ae051a5199d99be98a1b57f300e02155616c965c592bbed973f7aa4af2161fc863c8d12c3e94d56b28f032fec4def157e75ef07412b947d40ad5ea7acb54c8d7d85eed030cb6daf67d03baacd46d170f4c5478997ec072a0cd336f3b66f026c68bcc82000342fdfb88eb7a274cb2287ec9e8f07f17f3c8f4650287e781d9ff8e0524996002bda5fa50b7b383aff89c8164b0015ae6a7a3d16e4ee024a4a3241ae63bef2a424c4268be8adfb604895feb8689c49f6260db957f506828301e30780a628bc8d301f5a7d3950835705b2c6a001bb8de12d8adc310a9620939ae6293f57f34bfd186c1a0c402c20aa7060acf62fbb9e3a68f516a25a7cbd10c1cb2d1b958e3f7e0168e0bbecc14c8397200cdc6772894a71607a35c0922e47205b99d9af8d527358a0b80fe7b22709960570a46d7a3f2edca0a9e0c026e6dd47c7da8c8136fc034561b3264251f0ca10826beb320fdde771fb7ff2c5db3bdd369597f4cfdf1626dd2d587a66b302d8e05312e22762d56dc23b610dc82c35f69bd8605b27a29982cba0e64ea101ddffcf400b8cb0a57ca642f96d69c73bc196e23f44ee28ad7cb6119358f1a319657a3f5517bed1143fc4879fc08f662be08da9d6e2cb5d9210dd4fe9f58419c8b7255757c3a099e192f1eeb7e8d84b959c3f0844b6294d43728e5c6a5291c68b7e2f0125392c5f13e15b942cefb1ca4ec3f8ab75918c663b5bfbd2c7534a06d27867db653b83084e878778037a1348c375ee484a4fa4a63bda8232cbc5c862e729779cbd6197c97088bf50cf1a9c8a6f8e8394a8eadded62a766cd8e934efbac310dd8c11556b2782437a1a7e2b1d3897e6789aa5f1bcaae2878e5869ccddf7fbc18ae615f0e607622c413dbe2b58512d8268e5afec653f50fb740e0d42ddc2f4700d707af09cf23139501a74674c14a86bb0b96821ffc7ebc6d48a93268a92f792eec44b0a2ed314d2011bc6558d1df415e6ee9ad1fe4e72fa8257fe7c52960972ad3f657f0e4658df065af6870cb07ca5210247982def301d0e71e590a635f855345a622e1c7182bb11d23ac191d8861cb474ba93925bdf66d8260932053f03265917f391a864c00cb4d133f1283218d5b9ca411cfcb58ee62bc3f5df3cff99d304e3bb22ce1241385c7c7b2a11f27522271cffaa69238a18e16a07dbbe06f69b29dc53cfde09565297aaa95d0e3b1179ad5f0f98f9a21e71145aeb085d65984bd90463e8c9932f3528bb67132fef9f40fa3e2cad85e25ecf2ae5ffc7563b11eacf71f84cf2cb1f209ab32f15c1c0f7e17fdcd0b339256c91ca8ec96cda209f654c41b2effa37ebe8cda01fdd7f676797170ba5d4de1a462243ac7c69b21dce5fa0135efc4dbc8b870c9ffa254012094afe203856145ea00249445396dd7d8f1b06be8872b0fc9cc4693cad45cb910c4e15a8c0fe1c40a609501255e4c3d1f17906665fc38690e8a6b0e4ea34cfbf47c7f4f3a637521daaf0b53f0d1efb6ea70d961b6955e2857037c2814156bfc47a6b45a896f01dccbb359619915ca38e4a9273beb5c61a155fb4101f1d51337727f50e327253a45563ceea9d96271d5642fd4ef945a38821fa6790952690e68bf4026e563bdc31bf4a89ca73d5ba16287b03ce336f9d7744e61a677427ae4800be3d034f4a6237048758882e6fe5612b41697affef0edf74bcffef0fa19a28a75038c1cb7818e14d08f5eb8d23e98b56d78944bb4c0a305266a0519edc720ea6a84487f65cd5b579b60ba5c8b4d5c2630ae01079d9e8e59f2214ca9418715bdabc24f430b35b874fb1247b53fd7112bcfef07cd3c4c05ea6921a22d4734c368e7a4f56fc74935a8a49315099b7c441159c71533d693ddd429560bd29dc8b73c914c145f45414c185f0a3d6ce5c372b15152563df06d9df5a573a97f4cc7d68d30cb6158ba53bfbec44852c2b3190f68dcb60047bd8038fc1ae32936c46bb60e0a7d1779d65e3823d43246c56701fa6f7b59923a9c2862a0bfb1eed9de0d0adc68d9999c78c00bfffd5adfb2aaf6168c986eb730cdeef1b01dbfacb373f0c397b17282d12db2dffecd8687b949ce654d8fc2359f46a086599f083fe924c29ab0b7f853cfd5027960ce52561c5fac9a0419f777cef1ca967ddb06fcf5109b1debff5caf2620588deacb42e1e091e0b3eb1fdfabdc82ce57bdad17e42542f28d1965f9ce9d591ac7eccd6ff80d9ff383663b79ad3d738be439bf59ecc527186128c909531b3d8d34faf8516d633a41746dd143ec891763a4e05362e9505aad34a7da3bf4d8b9c543a09940888661547e5b0f73b178256d78c33505449c10a644fe7970ba37a642d62c42f64e75a6ecfc195bd51ba70810467c78b8647eece44a7bdaa721e160f7b227f3f79cd9653d888a7ee73bad7613f4879639d1b9b2d368a9f7d075db31a2cc274ca0ccf8bd41142a65b4b714334a30b5c9b886f759a4b985618d23f0d2c3cb64a793478dda124dc40f82ebc1e0a645245a4f30ed6ecb52f7ba2f68b9729adcd6a873af5b4b6e74c74a035edf51b7faa563eababf0f8bc4313b824d254df9b48b5d1fa0196fabf6b5146f219de62dba1c7e9c5c98909f95c4816dcea23b2e2c8840e562a44e55550611ce6b526a987b49542339a73b0bf2993f8c5106338b9b5df3b6e61e48a664a074bf070622733f09dbe96227a823724802823a0009ab2132787a7dda0ee6bb5c202132cbed6ea48fe0ced1093e7cc0fad7d53739d0a057d0bb9161d6e48878e4fc8eeb35855afa6d296e43fd36a84fbbcf53e22b58c1bbfad8a3545ec5fb5f8ef51de6fc3d3e2efc791742aaa2947c10499980c8dfa8503f63e821c97a8ccd930fafb3b44f4919650a0b943604acf1e4e9939008f49ac91e82a12a6ee631b463fe2b12dfa35f0699b8acf25095d058ecdfd0b35e16c6c1c410ab27b3ab173de85271043da3a909a3f8512c04ae6b947a8fae5065913aaa1c3cace4c3e8cd2de13b3ecb2afce87a58469209da3345625943b977c7cf94b4efbd821346ce6853f9bf7a87758fc0a4a4d756783a08fae95169e59e41673961831d80ba808226c79833415f24c90526ec73aeb60c7974522cfea95cda72a63ae1ac31f0ba4f6ec5798ddacd4e61fea1bdbf4dc8bb08d26ef43cc2439f4313c707b21c775544a72612025e185341856fe881a5eeb19f42a80ee2ba8deb5fb355aefc1c9968a65646ff34f52c646e7ee4418f9284e97b54012a7302f4cd80a50151be3ecaec3041cea1206b8c5014d8851af376c6507a756bd751c7de39a0260a7fc95b7274a19c246ecbc3eb1f16cddcd41009411f49989dff4d00c58d439cc17541733158d8cc429cf0d748f287775c95d42d91b370fbdcb3c1aa64c380f641b4468fd981e03bd71ea21d4766a566fbb93bc8f1b277500826ae98819d5027a786d859c17e9a3823bc5ccf81cc05ab513ac0da7f75081051ad76675f1c6053e811b9840064b993c587efd215add62d7efb8825b251cf8ba70ced442130acc98b180bfb0c01a1ef9fdf691808ce20b30aac8d8eebc193d3fb184c98a9cb2fb68daeb8f30b68db5df86578304468ea4814fee474a38ec7c523ec66cdff14d2874f3ef6b8647eefba9b9e1e3e155477be92525b1d4c6d0799b18b127947cae9bace49d72445fe2864c67efd38f5a031ca897a95bcbae1fb45adf5a227005a436e2d77b7726ed50b154ab3bcbf0baf8e47711ac05fd24511a6c5ac98109abfa4bca34d868e90452b855057af14c30f37690a5a0c08d561008524618bf5a6b39a805ccf129b53e672d39cb404e7ce98c136298e091d378418bb75e5f5630a6fc1a04e2d0f9a298b4c38b397b2834c02b4c00fb1e6bd4450df9be9b49e7a48b83f6d19814957c9179ad6de08f46280e15a7b5479df21fb104039b3172975076504d028f112873f84a17f7ad4a5c636ef1a936afc81799bd74ae81a067419c7c9c5f296a79a7862fe31bdf53e6c0c3330cc00279dd624bbd4b8d3a1040c8ec2b37741e96f92658bdaa92b2b4049855e1baa2bad3fab83eb3295d3342cdf8c320e7e7fbda578860e4cff5e015061bc71427ecccb47bb889ecda4a242009cb2d3adb1934d7023b2816a93a665d7d92a46a2cbe3a2fd469582890f6e4bd4955a4b65119cfe3186669fda35110bf5ed3245fbd1a6cab20bf8197683f40f5ebecd1d2102f3b5d66f5ca4335adf2f0bcc9491ed7c4e1d47b02ba2f8de1ac387d8322b3edc6f385582ec6803fc15440018493bbff61eeed9d6a47ab3101baea3bbc9ffee82e6d06910ec460825f0a002b566fc9540760a97b6dcb545ce44775fb2f5b3e96b7a74835683f0d6ef3d7eb9f1ae376e610232498f83493fef6ee722d1fb31cb59187e4964a6908b2fcd491fb5a52e60c9ebb1cf72060ddf603ed5c79d24d353e12929137423455f40427c9c8ed04722823ea7c6e5fcbd5314b6337f2f43bd15f5830d486adc7767ad4d4f5b685993e32ce7428475bbbf263570ce915a05cd702756d00e7007cc747c529cc611543bb1248259e5c24965850a60c3960b0c56bee41257329d85e5c1e10e9ec33211b22e2833f4766bd6e4042e71e8e8c2595424e8145bb94095e8bee8a0f0d637fb01cd620be49d40f5ebebb7f43b241f646a7413ff2a2757ebd57038f87152cb2b2226cbaf77f12ac722bcf99dbbf2388967ae81a99b91469310e3129cb67992c22e771c17ddfcb2b543387a144a6b0afcbaf3dce0cd2263e27bc1a8661de648a708a3b441405b7c76426bc6fe23370d7e92a2c7e74fec488ff0c072457b0a0239ebfb6b97a0490198adeee277d13bc270021f9a4112bce5175c889b46a7c6182a7785f417b52d527028187a51a819a90a3b158e40131bd88ad7648465d89eb4ff178f70f9a7ba64c26fe113e05d5a95ba9130e22c65c0c33a206a0e8bdef2582dd5ebd823eb2a9390044bae685b821b003b3eb8c0bac903e42a1f7639e8f5426e0d6678eec56a80c45229b442fa63d869c927ca3d0fa4136da23b9861e7a24f74a836727e2919db864a9fa635274d41e81e38ac8935dbd6e72000b624867e9808bad3e2e08cda353e3a51e68ef9b53f4faf9487e03cb3200ba30a2e4ead5284263e513320529ca8362e021bcb77b9a15dc48c1685d2d25c3ceb736b4cbd4075c581b51dce7911e9a6a3b4c48fb8d11ad8f7b88ff1387f999b4b1ab2827b0de4b5acf999529298b9c998ac0209ba6eb24fdcdba94adc53620b042224bdc955f25e5b9e2b90ecd00d655ee307d05bdc010f8def9dd1c6b7b23a3d0e6b97eace6a84bd3674c618249347016d096a37fb20d7136de598c29e4d2fb537854f586da4b9203bac44cad247ca56200860f9780da6c44807b9f41f60e200c6efbace4400c6ca63f9889aaeb7fd3a7c484c22d3e9676b158825b3201b33c74c380745e72cfdf83e86ee59d0511ce50c3d1e1275ddee7cb611ecfe339d36c45e0128e7dad8c070b36f095ab1ba6c46c6da0d94968298c3a28dc779d2e370986a480fe0290742f0a25adfda8646b8813106a69c5d3863d6e638ccbeaf209ed0508e52a069b02d3b12557ebb97c938012024eb49b1044dd3f0b6c01b94dfcc62e6cdcf3457f2958e9ab7037f86639445d6b18e5683b8d2971e6a9fe9a5502de56d24eeca17cc1acd6389ee8f90999c2c8bd41af49b87c231ce753263af16c16fa9c954046f9696e5ce4e621c412a48ff8a60df49b9d47f0f434abad52810d7cc9ca351ead24c9a994c84dfedefcb6b72ac3cafa2c4f3e8577264002ce307406687189e9a98faaac544b868061529ddc68c16e524fec9fbbe2a96a670e517cf4d32d660957e07e3a563f3e6433a7aba463efd57d7e12c76ceee8bb3f434af92faf698280c001e398ad7c298c834e5592bffef04bc268bbd71eb957ec384727493187dae11324568942b6cf67bf45313666d7254a62ce45e17ec9afdbce14433bdca833c6a3d860d57325d6c717d033b7ea8d1845cbf71119662ba9ab1c98999f0101c0778cff2ec2bb09e0fccd3b2264e330c2cf7dfc647fac564259446b1646d835c446843fadc30937eeefd133aee0747a4cb9153804f096dadbae0beea8af8ccbde9545d2125aab6e9afe19492134d1cd4256d6258ed4056e47fcae64ee71c992d020717f72213988805271c1f658b5d5f370f59f7dcd517183b685b6a00ff7f044132c0da3f1205b50dba56413afac5515567a61937ea521919b072871ab150590f906d7c235d7277e8a0547f396c3d92903b97eb5981b73e45d79acb3cdbac99da9969471e3fe8038f879e209e2b4a34666cfa5c5109b1cbfbb13475230e801e50963854bb864c1302a042909a0fd1bb2e52083eb78878a9a05e680af663b286688b1755112096284e81b95524f52db49f03926de4463057028759763c85ecabca5507f16d1cb03635a1c2a617dca9e5bcd23f5293d420ad161fca34395b3667aa3fc1d2c6fe61dad8f4da641a3eda350d3a8c3dc2fdd674ed949eaf20c0e0c598cb4f2fe3d710039364ab7bc53b5ead379cb7bf28caec0b452b4d537055b5583faa84dc32f90f4b6ebf1ae220b952df434b22686160ed886dc93bd2f179f3045ea17907fb5a67c39efe22d5d72bf68ea87e69ca30ce0713acde9c150ee8772a4fc1c8ed7369f3544261bb77e72fbeed676b152e0629c750fed501a74d76a1b21cb0251feb5066f1387b36ce3b944d638d77546db2931dd094c15ba289251bf0d76b39ecbb5e07df7b5bfdd494fd38b8c9d1a19b7800cfd3780512ad5904c600886d6200bd9a93c5b34de4a04f4b23a1d93a6b294691f30551ca9a3a184be296cac278dabbd09412aefe272d025ce03448d3e233e9269b7a791447fa2911a9fdad953f7aadc3db7dc931a7c6cd315c2f851a050ccc849e486ff4816469ed98b307a6c8f4ca907cf817d7750755f116ab56f08a0fa8741f8e93b74a2a04e5d819733b4b862800d7875557f4699ad0762a9c3ab9e95796cb55845170ad058ee63f8036a30d5fc1b992c901f4894f8f943372836235b15ea3e8345fc5d5fc073d3917e8b4c1a9b97d1e24cdc3b3e20090077f788dc43c3b340384b35767b4bc40cb1003ceddd92fa34d143b61587571ab824090e6e2cb47cf76ea5da0f6c9447b954c766d3614cbcdaeb48e99b501dd0042314d26ceee01d14f971ff71d346bf4d7c66926df9aafd821973421175dd7136db58948479eeb03f74f455b989a525cb8ef31255e8887ef3e03ad83b324e059c185f3b37c39831c41f44a9d0a92886db938c5ef7ffdedacfc9445db66a70b00d92090aabbda04ec49e7a458c6b5b3773e862998b7ad0c0d9f572b1d9ea172fc8bde0a6277cacf51a2b70d80bdd4829def7694b3d1c893ed3405bec1b52622f8b0a1cc28cc915d1bf9e664f538408682f68a28158ea46557b381010a9871fbe124bc4873fc06d4f4df772624e033575d5f557823ad9a01fa565f4a8dbce61e2eab7df0c1d406b0e710fd9234efe14898c519417e67b01071192181a7b0c7b8bae684b732fa60bc447c878a9f4c97a5c34b9ef610af30844f389b148f69d547b28fcc18e89a0e3123addb873ed46341fe3e2f3a43a8c1057f363da073ab7b866bb4ff546e5d21a7617511b74af13fb7fc62f487d8227eff98619e3a8acbdb90004500a491bec9c318712e7cf89eb0758613a6db26746357fdebed9676146dead4c64163a7279c15998c4694dc6a7025ef2bf46f0af58828c0518e9bceca5540a01458e1528a4aa7b9f8e03ccf80f81ebe90718f949097f14fd844b421cfe03c09623fabb504c33f2fd836762202d7ad9e3a68c5679b636475f8ad219b8b8a4bb05df1181cf7637d6a9f830cb0381e3dc68b64ca28e3563e7e6a0856ffd93534f1cbfece96c59276627cea382c25c489a5d46c4e6c38c75c4914303160ae3e299d3ca9c9b165b8e1381c725cd5a154c16b3ba0b66c12f287134b220bc105b34ec3def6750c92bcf4520bd9800b5940e45dc6582e3b08d1b6db0f36bfaade93c977211663bfe6d76810bef516f0c7b4c9fb10b1e38c0d3075f03bb1d23e1b7b942d3d1e40ce5656d32e55ca701c404d5be6ba6e8c9c649690c443db825358c7def2f9bb5e3b7c0000001000000000a2e3b15bca00b93981df34ecfa85a32b780590c5ada84bdf000000da00000000d5d8ede162d99585443d3b88f76abdf75b523551eff4a6ed0000001f000000002046d2984c67754e4c3d76e3970b95ca3275636fda47a7ab0000009900000000f43e7fa60ba295a4b2de6739f242eedbfa89908defae0c2d0000008600000000909224376bfb7e4b872841330996b6af8a2cb80319195af0000000b10000000091afd8a0aa48fff3dd9c3c79cccf0c660696d85c104f4fb10000007a000000005f5d82dea7571b8f3fa4235352e51ff0e98ca4e7a07b76c4000000f300000000a0fccb1717ad1e3229907a4d48fa2e8e14da7c462a72d65d0000008700000000ebeb913a7dc48632e3eab07a8a784207142d461d37852066000000900000000079b9b2954942e2ddf6d768455f67b696c33576fcd4874dd70000003d00000000c491822722ef2743931cd5f5904a1d3a2fcc3744eb1b44ad0000001d00000000bc020eed2490b5255af300275a85a75d101ca166366394550000007e000000008e8b0b934fc7b98e57c6185ab489dffdee23bb26e3d97da60000004300000000d0b27707702d8a16041b9b23d673fd388becc6b2b8dd18730000005e00000000486abc1b2347ddbfa799316d29bc5d9875c7053629721d5300000048000000000d5242928e93efa1f09f931b26055d14d02233f58e7ff05d000000a40000000033afeb2779d50772882633e10fa8148c688f8963297cb6cf00000050000000001bd5ea881cb5b69979be3aba966686c97f774c44d874e8d70000008700000000c9b0e4d6a34ccbc21bd193863b2920263309adf983fae8280000000d000000003278c9d3d16ef3a6e660771d5a0ddb5baf61c83dcc0665750000005300000000649a9d974d73a9c0b6b1fe90ae088c47a43ba5ddda05f92f000000640000000056bc0abf8452f080b11ebb222db01ed473d9d02530128f4a0000002f0000000060cc16a84b838f2d9471cdd1a6e3c992dba81bf617dae1e10000008e000000009049e1ca2d8797931fa2d08d9fd0708c5bd9eabf0d8a2e8f0000000c000000007f918378c6caac0eb0d374668e03cfc1c51ff9b75191decc000000750000000055fb4b3ae883280cd4cad9fa1c037c9c2a3f3de704f123a6000000b7000000004e38afe9dd5d072dbfe01a0d1b1c5841ffa0e4dfdbc12b3a000000fe00000000b267c98a31e5618a57768355f72ceef40ae632a07c2a575f0000005600000000ec72205d97e690714f4b3176535bd4740028b061fbe0f1700000009c0000000090335866f0680ba436d4c6ed3db17b35a3852bdc254089bf000000f9000000003295299a9fd5a95af721867232d169892569acb72dfcaad1000000ce000000001d1d011f2b011f2c011f2d011f2e011f2f011f30011f31011f32011f33011f34011f35011f36011f37011f38011f39011f3a011f3b011f09011f1001201501221504285801311201321101330b01340a013e37043e38044235044236044a2e014a2f014a30014a31014b2e014b2f014b30014b3101563a03573502573602573702573802573a095f3a02603533603633603733603833603a09683a01693505693605693705693805693a09723505723605723705723805723a09763501763601763701763801763a08763b03492e7800492f780049307800493178001d18000000e00000000000000000000000001d1c06ffff200000000000000000000000011e18000000dfff20000000000000000000001e1c06ffff2000e0000000000000000000014c2f000000000000000000000001680000034d5606ffffffffffffffffffffff00000001005c01015b01025a01035901045801054001063f01073e01083d01093c010a10010b09010c3b010d3a010e39010f3801103701113601123501133401143301153201163101173001182f01192e011a2d011b2c011c2b011d1901202b01202c01202d01202e01202f01203001203101203201203301203401203501203601203701203801203a01203b012009012010012235042236042237042238043227013426013e57043f57014e1501770908771008005c5c01015b5b01025a5a01035959010458580105404001063f3f01073e3e01083d3d01093c3c010a1010010b0909010c3b3b010d3a3a010e3939010f3838011037370111363601123535011334340114333301153232011631310117303001182f2f01192e2e011a2d2d011b2c2c011c2b2b0121351b0121361b0121371b0121381b01215915012115170122351a0122361a0122371a0122381a0122151601233f0901233f10012340090123401001243f10012440100224521004253f09012540090225520904265808012609140126101401275807012709130127101301293e10012a3e10012b4210012c4209012d4110012e4109012f2909012f2910012f3c09012f3c10012f0309012f031001302809013028100130020901300210013227100134260901353a4401353a4801353a4c01353a5001353b4401353b4701353b4a01353b5101363a4201363a4601363a4a01363a4e01363b4201363b4901363b4c01363b4f013739140138391301393714013a3553013a3653013a3853013a3914013b3552013b3652013b3743013b3852013b3913013c3540013c3640013c4057013d2935013d2936013d2957013d353e013d3517013d363e013d3603013d373e013d3717013d383e013d3817013e2835013e2836013e2857013e3516013e3602013e3716013e3816013f384301403544014036440140374401403844014129370141353c014135170141363c014136170141373c01413753014137080141383c0141385301413808014228370142351601423616014237520142370701423852014238070143321401443213014532060146320501473208014832070149292b0149292d01492b3d01492b0301492b0801492c3d01492c0801492c1401492d3d01492d1701492e3d01492e5301492f3d01492f530149303d014930530149313d014931530149343d0149343e01493403014934080149340f014a282b014a282d014a2b02014a2b07014a2c07014a2c13014a2d16014a2e52014a2f52014a3052014a3152014a3402014a3407014a340e014c2e02014c2e07014c2f02014c3013014c3113014d0207014e1515014f3a5101503a5001513a4f01513b5101523a4e01523b5001532a3a01533b4f0154283a0154351a0154361a0154371a0154381a01543a4101543b4e0155354001553640015537400155384001553b410156354801563648015637480156384801572a3b01583a4d01593a4c015a3a4b015a3b4d015b3a4a015b3b4c015c2a3a015c3b4b015d283a015d3a41015d3b4a015e3543015e3643015e3743015e3843015e3a53015e3b41015e3b55015f2a35105f2a36105f2a37105f2a38105f353d045f3541085f3542025f3545015f363d045f3641085f3642025f3645015f373d045f3741085f3742025f3745015f383d045f3841085f3842025f3845015f3b5301602a3b01613a4901623a4801633a4701633b4901643a4601643b4801652a3a01653b470166283a01663a4101663b460167293b016735450167364501673745016738450168354401683644016837440168384401692a3b016a3a45016b3a44016c3a43016c3b45016d3a42016d3b44016e2a3a016e3b43016f283a016f3a41016f3b420170283b0170354201703642017037420170384201703a5201703b540171350301713603017137030171380301713b5201722a3b01733a41017314580174354101743641017437410174384101743b41017413580175293b017535520175355301753652017536530175375201753753017538520175385301753a540175415801761558227709420177104201353a450100353a490100353a4d0100353a510100353b450100353b480100353b4b0100353b4e0100363a430100363a470100363a4b0100363a4f0100363b430100363b460100363b4d0100363b500100223559000100002236590001000022375900010000223859000100004c2e03000100004c2e08000100004c2f03000100004c3014000100004c3114000100004d0208000100004d0307000100007542580001000077093e0001000077103e000100001e181806ffffffffe4000000000000000000011e181c000000000038000000000000000000001e1c1c06ffffffffe4000000000000000000014c2e4006fffffffffffffffffffffe1ffffffd4c2f4006fffffffffffffffffffffe1ffffffd4d303e06ffffffffffffff87ffffff000000014d303f06ffffffffffffff0ffffffe000000014d304006fffffffffffffe1ffffffc000000014d304206ffffffffffffffffff87ffffff00014d313e06ffffffffffffff87ffffff000000014d313f06ffffffffffffff0ffffffe000000014d314006fffffffffffffe1ffffffc000000014d314206ffffffffffffffffff87ffffff00014d310e000000000000000000000001000000004d310f000000000000000000010000000000004d030800000000000000000000000100000000553a5300070000000000000000000000000000553a0306f90000000000000000000000000001553b5500070000000000000000000000000000553b0806f90000000000000000000000000001563b5300070000000000000000000000000000563b0306f90000000000000000000000000001673a5200070000000000000000000000000000673a0206f90000000000000000000000000001673b5400070000000000000000000000000000673b0706f90000000000000000000000000001683b5200070000000000000000000000000000683b0206f90000000000000000000000000001743a5400070000000000000000000000000000743a0706f900000000000000000000000000011f2b15011f2c15011f2d15011f2e15011f2f15011f3015011f3115011f3215011f3315011f3415011f3515011f3615011f3715011f3815011f3915011f3a15011f3b15011f0915011f101501213559012135170121365901213617012137590121371701213859012138170121151b012235160122361601223716012238160122151a012410110125090a01265814012608090126081001275813012707090127071001283e09012b1012012c090b012d1011012e090a012f090b012f10120130090a0130101101311012013210110133090b0134090a01353a1401353b1401363a1301363b13013a3514013a3614013a3814013a3953013b3513013b3613013b3713013b3813013b3952013d351b013d361b013d371b013d381b013e3548013e3648013e3748013e38480140293701403508014036080140370801403808014135530141365301413703014138030142355201423652014237020142380201492b1401492c0301492d1401492e1401492f14014930140149311401493414014a2b13014a2c02014a2d13014a2e13014a2f13014a3013014a3113014a3413014b2e3c014b2f3c014b303c014b313c014c2e13014c2f07014c2f13014c3056014c315601225915000100002f3d09000100002f3d1000010000303c0900010000303c10000100003d353f000100003d363f000100003d373f000100003d383f000100003e353e000100003e363e000100003e373e000100003e383e0001000041353d0001000041363d0001000041373d0001000041383d0001000042353c0001000042363c0001000042373c0001000042383c00010000492b3c00010000492c3c00010000492d3c00010000492e3c00010000492f3c0001000049303c0001000049313c0001000049343c0001000049343f000100004a2b3d000100004a2c3d000100004a2d3d000100004a2e3d000100004a2f3d000100004a303d000100004a313d000100004a343d000100004a343e000100004c2e3e780000014c2e3ff00000024c2e14000100004c2f3e780000014c2f3ff00000024c2f08000100004c2f14000100004d3041780000014d314178000001");
        assembly ("memory-safe") {
            return(add(code, 32), mload(code))
        }
    }
}
