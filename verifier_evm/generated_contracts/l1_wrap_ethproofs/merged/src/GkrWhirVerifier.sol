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
                mstore(add(IMAGE_PTR(), __TEMPLATE_PREIMAGE_FINAL_PC_OFFSET), shl(224, 0x202d0400)) // pinned final PC
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
        // register final state and PC in the transcript preimage (validated in the Rust mirror
        // verify_permutation_identity_no_inversion). Challenge/addr-space/index constants:
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
        bytes memory code = bytes.concat(type(GkrWhirVerifierCode).runtimeCode, hex"00ccb4ef702165927a3c003407bb9138bacb196137057d3aaa8e24c429ed515fb02d78b777ef60396722f13829dba7693edf52813ef15f34812381b8f838d426fc269f342b8875bea8f50f457284e9b7ad38e50463f7359c105c2765af024c5a6e5e145efb5da3d49923ce47f8a6eca41ee8f60a3c4b148487859aea3d0945cee8fcaa33d4805bffaed3a2b2e73453eb7eeb4e9fa7685e54efab05bcd4165f49049eabf6c722b21c9ebc9d8f1e7e472d9fd9d5ca1df56a404e2963d34216e879773f040dd012fa6f1e11a44504c15a6ec5b3283b443e990d9855ddee443106ee3ba0c5c0105aefa1f8a438a0eaac2b8e540e9dbc557b10e9ec8250d5003ffb4de17e5e175f4622e5c8fd383a5d2ebdbf1f3d5f75a09fa23c85c33e759880701f91eb5ef7b68efb1028b5ac2940b9fc2e99014d7373616d3d36151b7e5803c1b6229805df6f8c5e064bd419e5f6589f273db102872e80fced669eaa3ab9fd6dca1b3e3e671279a156f8b5e7c5f6092b7365b47932c8fe9dc973c3c4cb476be2043c0df9d70b29de9833d146379ef87e6b30e014b7744c6416d53e8846295bbbe6515a25c190d80c0ffc5beb44dd9c604281cf270752c142f67bab6d982474f41942a3f45c5d7776f24684b3660fed65e0a69e674d66b7569da56dee1634e50ab2d7c8c1b095fd728d8689b6940e70a3913dec8a8f19d745b132cfa2fbfa7b94e0bb15f02ba1b4e226cbb8b3db74aaf2c3ca4d3035bb18a9ddb5e7b06b1148a0ec5047313edeb8fb05ad5b3bafbc9543ff04f86d1d639524718449a2c1ab7aa6146bbf0899b21f2d3a795e0f2900090de32ee60b3eb8c9df77335d6f97a3d4f8d4d0206b440b5b8aa3d89d7f54b6874b7bd8d2da5399722607d5f05c4528e308bb30aea93579225091ae4d90b4bbace8c9c85d8f8d94c622d23e4c5dac15ec91ccd26b9ff90860725db550ec523e0b9e5cf38c71b5003156ff1e431dc7ac5e3a9acf269d37a9296c02004f0658297e97441dda7b2ebf0d804d85c5035698152939e8a633c60a5a6bb2226bfda79cf7a94bd6cf83994741c2573d9c6286f54a73bcaacf1482a60dfc88d87494a8dfc55fb1e3f6aafe70d733b88b3115d7fe5cd97a54675a2518c6a4dd940ad68ea6ad05ec4567f71456f3de3ad8f4f15dab629f11a75eae3be4a8ffeeac3428cd9b8e50908e06e92a35a40896eba59fc790e5d94d0c66d60041bb14be51bf841fbbc7055cb58fd2d8a286196a7e028d88a0123bd7482015bb283771e29d5ae2b11239a746c997be2ec8ee57eafc2c660cd1ab30faefcd0a5c1172ae7852fb34351a8f1d48102196254c1a0cf85504623d4522c826d4cc3ab8754cb1ebd40a7722cdce7ffa82736bdfa47336f4ea463eab36e57ca0161b6862600af96ecc254473d349b07b05b0ad4e5f0221a6f5cf13f8b1eac741fc9e6e0bd7f345d033519a0ca476e4fe14250f5e39754bfde4981ac3c54ca3aff2003fe39bb0a379c99f3cc0d72a0b3f9ff2a717c5d138e60b04ff16e5a74121bfdfc1978cb24e014b7feeb94e8640424bf6647be0c87990615c791d82f5fc5d6ae73b40e8f583cac7848ce45ea563c0e70efe8b47aba926d1865a8ba338d4ef1963a1458c4a7393aaba702ae9d8c658aaf1d34fbe1667d9e93d78765c8b6d3e2cf8b14740d7618bc1cc5c032cc17e8951bd01d8708d0af4487c4e4ac866a7cafdd7574f24513f479c3c0ae96500f3e0b9ca5c5172f3080860ad490c4b15e9c1c47af447a3d3adac973a3ee095eeb3fefab2789d7f6163c9830499866f8d4a3e63fcd5c82ac81404f2ced0ea1fb33c029e952a99be9a2ea82ab477baec5110f68588208df275ea7f427b9a731aaf9a2ba78b47d9ce4ad04a68faa03950940ae870b8c329dc51d89edb75d1699cbde9b8d10f9f9e39baf721a79aa853c0346aa09a8ca041e7c1566908e88cfd1bb866f10241d389f94e41ed91952c7de2ec9b7faada82c420f05125d2818175c154471f7f67c2fe48c828a8a001d5ff3a31b6b1bf35cbada575113521da99526c32e698729ef9da7bcfa7ca479a93f42064b071ffecfabe83b7c6f2746bdcdff5fca0093bb9ae5899bb7c3b1c5d89d25331dfd7592bdec2e0706ebe0709a8cd34b332756edb1a8e8a2c26ff8b7a4bc4fdd47c4dec6de4d0974de837d57d6a130be140b61a970a728d97d3aff2b74075ebe6dae01ef8c922d88cf786e2bcf0333717df9272c2fa7d38234871f687a818b6d1bb8fff8ce3f629af9131f868cdce0b78e33ba426e409f56cbafc23e4e6ee087df5b2eefab9f0464dcab2bd8feb7721646a861de6c56f34a3b212d57835b3fc61cac39e3fd77ff3bb9ac83bc4edf63c1882fa34ab72b35a7930f2569058fe134985605672d4ad700379a3a945a7299e163d6923ee598c5cccc88b8b75fad46fcf0892b50f9cffe6aaf6c5d86bc0e1a3776f0a0d1f037e5454e4c5ad30608dfd63ad6f4c786167cd6e3b316d98cd39bd987d1091ca035f84a9cc55e03d5a7a48edc97fa0203a54c5509348f5a9914756a484c674e3f91ed81dd7d02dd2b08e5356c53ad848344751eb578c2779a9721942009e40ee225be380cba259145e4393b8b60b80b2dac06ca9e81c55b54afaabcd64365f8b4aca6ade5e3b25ac5c550bfe9c1eb592939d2ecbb2decb0e6d28f3da5aa278dc462113c323f8d43baee393689f9bf196563c338f86ff8ee0844bd5068d70f6a44227bfd877eaeaa241347bc032488dcc55ac56ceacb9d5fc114ceafea6f48444b962c76762c5525bb8a7a11cbb4ae3b8e8aea396c236fcd813c26717fce4550434690c2d56ec90212d62241e1e1d76f9f5292ee49c229175a22b2b91db5ecb16adc16d492b57f42b08faad364132eb276822bbd1e4f15f8902a9aec6bba72aa63807fcb313d5fa96f934d97f3c27b312e74f88cd72d295f3645036b948824af9e91ae548ce9fdec8fb6368d54b3adb661d6dd9a563d935400a68359ed921e54505d1a56b1926529f7bf3e8fea1b7839cb59275e793ffe4b2674df75edee62d997b8458c0a7456045e054c8596836f7dff66cf7cc802b70eebff10b952f32f636828c697dd3212de8ac13bc7c31df304a7773b8d5e8eea99be14b49e96393e4b6bfb0ace284f5b2a298500d23aeade3d8a37dc78157b8d689e510a27d59aca60d5efd55c5a3a9ada2f7bb095108857b13f1c49b904e11b0da5605a19b5dacb6fcdb0c088b019b41992561f5be3501086cf113686e6cfcdf6318076fc1eaff9cf943f3fe1af9db76b16857d9535a77742c26e7592b3c6184b8ca48a2ed9cc4d8baa074e272631dc3ff9f6f36809fa3b78b1a3e25da2970a2d694052b68a2e902a4b7329b7cef2d9133f5606131d2e71cb48fa8c00e1ef81a42c02dc1b3c3916c8f99cc74ce6c8118a4da619ab9e62a60cb746aaf000cf16fa44e9bd40b9526c7772831d5ae48a431c3638236baa9e950fd54304f6c820f7d60ec8cf4a75cb0e248640b742a1a8de4d65717c5de6776553c6698e9b3452797800b5c4efe3305a1659ec0f90d4f13bd169d359c0a5557ec2950b79d4708ff08c55df1ba03fbe11b6468610728b24c6b2416f33d3bd0914aaa940e2115d9117467315212477ec0e3e44928d0ef5337324bb5602d7c6fb8c72eced9aa4714250e75262d50d53e20e3ff24dafced1f0bf0290a0676bcc7557e52cde87aae0508bd607ccb70cc1b4cc6fc162b3d8b930a4cc79445ff2a1f9f6b46b1d2066b22e3728ca0f1382fad92eca8df5188c9b7fe37bd1e1d883fa59f3fad26bb0df22c9db17eb22544d605e9d549822448390cb59f1a9cd240bd6b81aaace08e95a20c42d42e398a4ef45704955b214a0dfb970ac631b15ed279af63e3419be1a032f325077ae4645d3b90364ea23e597ceca0412edd285df3e83ef5f545b9859e956adab2d2d0e4ddea5188984f80ad3e49fa5faa1d392ce564c7f52ec6c39fb2f74653c01684bc8e5656722a8fdb12ed0ba6f9978339c016e56cc736074351dec02e8508bc33fc9b45d944639ae70214c9fb4c406b25b0a099507633086e26fdca8ff9fedf28c0d79de4a423348a2372f6d40466d8c5b402597baeed9c5772ac20601c68c659dec9a91c265f5faaca6de3e8620e1ca33d2a90b8b9d26ad7bb741f106bdec3e12489af9fe93876ce6c623560d8c819d04356874bcaab5e412aaf13554c71c5c8818e1ca586bcaca3dacb19c32424c47117605c10b9980b32141a0f1d62175bc7e6b537800d7e614d7a0dcf61c56fd0c63d48798c31a25e5d918476bb802af3e9a963fb555e7814a95687f653bd76eb76ec6706478f3d62f04245e09ee5bb8f638405d9cdae3fdc96b8e3a10a88223f26ec293f2ebacefc1bcd6e51281641c1328d8a0078e7539f5fcae2da033721a31cca9d6a32efcdc52e64db3a60049023a4c87a363dce27c0dfe8865cc1767e8edccc25edd93c8c23b32d1d71a294bd42b6b425155f9179bead27bae2e03974c48058f0f217af8fab490a96b6c289d127a150813f32d9a3cd86931ff9cd407ee67db8e0dfb6a55c1ce3ef27623740b1d0db7b34c1a8d90c8561abaa674d8b0871ec7d3a0283d10e7b07dfba0c271618e8b86b76cc1052d570eeaa93142aa4efb732d3d62d020d8f5378f54e08f3f6b3cc0309baac24cb253b1332bf3ee0faf0a83c27025e735aeb12556674b9128989788c78526193a7dacf94961863ee70b7f888fcce034526d8118e7a7469a9e5a02adaf075684947ffadec91b15fa448cf2780495742bdcb1733d70b795c272930b77a39d952c9f60f50543f42d3853e492f3fcbb4e92706b7f2b89ee16dc89c46a166f2d31e92aa7f3f69078ed98cce4ad78dc061f7c4d2930bb5e777049e81aeeb02fd7541fbc4a74d5b9b1b800644d157725c2d85f0499498a2f512061785593e1468335aa5516a2c9abb00fe67ac167b7f751c69556549310646d39faa952140737fce4e9c2e011178b976c8e96c426b35367177c1d108c2f409f0bc7775b8351acf25f5c26031dd11e171e0f9ccb8426aa0d7ba46d63c94687912d3f3691bff6fc379f27fce8363ca466804c9d0a5e7447dc0e56065f2c86ac3b86a5999b09f8fb1a32d207ec9f044aa42dcef977b433dc6aef2425a3e8827970deef0297e359d95aa195615405692868c8c88420539ef66ee664208411709e1495efe79181e966be02becf67dcbfe8f33b587bdba74537c3689f4c5dc6cf20803322b588aff37acc1cdee8c16536355bebf3386ffed60a07d7178b219258cc82d379b1434d391efbcca66c1bd9abab4b094fa4708bf48b4d00dba1fa560ee0b812bd8c4135c7caae8a8415c05e9df744f3c882f29d0a7caf3f1981ca6fc90e44d3498b8ab7cef7805e75d499c3842cd1147c8e4d1a7f87199c706aed567b2f4cbb35704ea4d1f3af04c308da9e10e30aab957f1bb31e8844fb875109bf7258c2e6084adfe8b1dc906c3679ea899f28b62710a6a3e00d5b501138daf683a325aa62d14a218282b92b886d4d6a72d486be3f6e1539b901fec9654f941238deb75ba60c58e50a21c468c162ca3c8eec8915fa5b496bc95c1723aa278db573bb3e9f78c615fafd2a1d347cba789784ddbc2585049cff0c2b1f570595f7013fadf8a012cac606f0effbecf8bf01ca29792a3e18c2ae52e85ee75d18048520609405c1f02116b0db0b30c8f84f8e066fe9c07526105be74ee655e5ba3a61a7f16cd78508573e588e079283f6eca8faff1cead49593ca687b492d73dd2c5926a33e30af632b0686613d0a331beb496a7dd33161f08d86ce6f316cbf03be181cd72dcc40734348bd176ed9a849c265aa210d0de9ea6a6117b5217dd431d79686c3c8b4c4e3996f4183d5a29e4304529b2814b9e44f4410b550fc389cb0f2166aa311185faa97f5b52d7765a7176f9dd6faa1777b934690b4aceefd0df4afb62e9cce8fa2f5992f7375904c25158433500dd6c4d74feb171e4f09ad3149ac4056fb2dc439ffee580351d777d047eefed28148d74a42d2cff417d9a3d6b682e8c73b81f7929833cec7d960d935a5e1dc9202d39c31565fad5a357076aed392fe9f96c0088b68e20086f4bb42762bd1f8044f0d6560c3478111aad80fea9c8f4805d86d2bb5bf440a54862d9a1eacdfe79fd1153e8f3058e78812503950b32b05b7dd947053e60fab987aa411902a31a4ab8966acfe31abc83b309834c22f8fe8ae8fa826948d2b99b48b0804b3481f08be448915f0001a24977cd989def2ffb1d5f60830a25f904cb1c1807e482f6b146aa3ec313b5cb22ee0629c4036298ec0bb8d596215f67d4f00fd6dfe66aaedec08e281ae6eea7f038f2a078c6ac5a3560dacd8f8bf0e2f1cda5975314b3694629a8d0f970f0bdf6951982ff45daaf3d31eceefa45a5ae2e9601602482ed64f0f9733c2589bf78ae6167ee1bfdf1e7678297a7f831d32c25282f94aac9e5b762b5f5594a3a5f847ea282729b2509b4137b85fa4c1c107ac8d5012ac64c1087feb0a6a55dc097cc7b09969acf2f3b45323fad4e12ea614dfaad993462802be19018e19a99c92a2d688ce4389c2817b79ec439d23f1bcb772cef12f6c1e624483b6b8efdcc17911e3bba459c571db8753b1d956309ad7df6a2da86bf9c36be95c1a65f363cc162fc1d0568690bf13e2f5f9c386da3e3c87863a8b3dbd5cb4797b33132e785e5a070fca9ffd3e778d7065cd122d99b83dd1af454493e47619111df85eba1ea67d1c514e0bd7506034a387aa42ebb0f81db65ef05cd8166b253c70683ff13967ea86dfa319cb1ec6e515cf722c72726fa71e13880e606ebf59323a23a0806bc0cdb2d03e514294004bb39afb227b70d9ee6c44869e49bfd659ce800b85ce526d01f5e2c7a587834f1150b64f9785ee6df4e6f117895cc03ffbea341404c91bee5320365a60f1e133729e26c46a0aa62cb6cc083bdd1a9cec4ec565cc41a499019174bf11e608b3bb3400d39de9aae8d2b64203aa9dae92fd1beb12c45f985fcf469b97aa8494042332b6a46e3ddf4fc58b4bcf06e65cdbf9df4e0bd2c17942bf25f6cb8e5ad68b1339a51817bdc8da91575f37cfb977353a342ee6764c7fbba6fff4db3fc3945f6497cbef7a657807f122c581d264eb0cbc19dea61cb950397acbf416d7f1bc9b12040ff66be6a715937291d72293429363d97b48696f9acd17511616a9d23078f9011e8180f05c19f0e264175c0d73160abda1a470404cfbd4461ffe38d97159b93ed4287a9a7de866d2d3d989aadcdc280d4265ae74033461359aa9a866d97039baac34c170c058a559f605ebc756511733072f7abcffb0e8cea3e5f673fa58f26f6d9d111ea90989bf76cdb75e0efb0173bb1d2ac0d01ab128c88bd780f51403e011e73a410c60b99d32b18784f71eba9b4bf5798889fb23632643cb11dc0c14fb8e7d7e3ea7c1e75ea43341f514ae73dfdb5251ad8f5cd1d6da1d03892e4419a076d576ce17a887de1f07386176c518111480fc2805011b7802a3af03dc82fd535659537533ec6dbafd909a1562db74c8515a8f96f920faf236bb92762efb49abea1da05f9e27a72c118d95fde43b38c9f4b3cbe864dc5d6da70ed9a7026b6f69eca8f5747377f59786c4e6731baab3595d16ec6fc7ae3d4ae5a030b2746e8a5af6805d7bd359cd21bd89b5ae6b428eda27b4f28a5bbc77f0fdf79cea8eb7ceeeb52356b24589156b270ac910f9e100a53963c1e448042ac7a8ef65a499152c44739c1ed481d103c8e67731867e14c19c9fdb4bcd161553c5506514f1f3acf0d2a0777b0da9a29d131999f24580a3480bded2a46581b7235a7aae27d62d5190db2a4d451f27cba9835f345aa81d5cb1f9f48cec23e7791b0e87da99ccc987502fdfd684fbd3eec0f9a7ea6a033d4511190d77675deb186146a68f33daf018b6495be43b62b01c01e99f91e0c87daa537fcc89d3ced07729f5e1327949df151c1427d54836efd5f7975b92be5af59bd7ea0fd2898ffdd435fb7959064946816c9fed4a7a83c0bca1a2b69265349694cf9a1c33f7e126b868966f1f6e695749ecec2903ab12779b85e80a1c46eb9513213515b14a084c393c362572cc793bbced7a657a4c7a4f4d27b91368effbd2b0647d8a7b2cf03a4477ad0bab54f78f9516041594613f7ee101479f5d1839e7b706575bca3ab9ad6218d4a57c1df29124b3672f3ff13b3c1bfee6732283dc71ec5ae0a3947d0e314f787d81d99b724032e6c5a28e0c0a95e31dad02ec203c8ca42977278e554dd6367efb0b69c5aac0b4f90cd5142c3296c152bd7485397cf797e95dfd7efd49ee1d8bbcbad23fa26e01fbe4433d550bc4dd4c1057cfa0bd08eda3ad5dc9b3f26ed6f2ba2d67fc36d3d2099636e8d0bb58239012a62c4c2e4294194d77e976284f33273939a3d63f959ac52f6cad416a947fea6599f8d976a812f4b3de9bc3175afcea5b6339c95df989ba79971a8feaff6b2ab38a80fa61aa22b03455deae00b2ef00a5073ff28729c0802e633a9aefbcd33e8d3aa24b645b75c7dd2bd2c6da5643b71a0af6afecf29b3cb84e3172af1e4baa1a2c4016ac77d9c283fb114b0fe3f775181df241f01260ea4a4ca121d914ab7579c01196806768a2753ad39e246751bf60f14d2ce0618e217fafa9add012457248a42aa67a26fb144b9cf53cd112db7e47a76dc9f45adae9a0a13155f1b593d0f0663be2a9d6ee4e7f7a0b75cc3e79bd734c5a7ff8e0a6f8fd24463c6b2f660fddb8f77c723833da5209e04367061f5d546913a4e306035296841b0f1c601248102d72f385abd96d3beb26ad57086a9baeb323b1acde4e982bb4982d8509b0ca3da06309e19511b6ba68b5c8848c04a6227806d043a3f5df91900a7e9dc7ca678bec004b967cad5e48729eacb19516a4a8f126127531b250983ba9aec5bfd02f65dd09eec41d9f283ea5d383b0c7bf1fe11a669d8a26732b648bddfbf199c074697b45c59c20fa3cf036c830a546d2a927ac2f5dfb7d317b471db3fb5dfba21269ab02dded864a7a2ba1f75dc575c008c6e3791a07db62b8b6556389af6cf16bc540a10b006631c8bc90baae6974310284feb18806113bb58738a63cfe88c8b63acaa880f58eff8a420f855568b8e5be7c40458870744ff2e9cd509b4d9c5303c50836e985e48747645d6d7490ae8d6fb26e4ea4edecfdb46346414737f1b8c7cb38415cdec9a5cb6ee242fa05d53d8aca4378e383c7097123b0993d1a33decd55bd585c7c5ce77902e6c996c84469dffae5ea40f0531dec7d3765d4a4a2e76c164914bab16d5c81869a1ed3fe8c5773b73349c61f650b7cc79706b3787e16d28bc7bd2bfe12127f8bf0847687caf3b78d4dd8c8f112acbaad3eda90275e9556b0fb660564906add3c8090103611e9f658b7c44eb3d68095cef1177ce74936d75e43157aaf2e38f516bca3e2205df4668cf59bd09b045f129c2254ff0d0b92a5b8735da142d20417e1e0e73106cdc0adb18b36c8557ae9f9744739210f790002b6322df4488407ecb85105fa09600e5fd7e900b303803d78cb87ec4126e85568a676aa4ba00389a7367a0dc5ec9c13b5aa01a9b8ab5f3e539e78ddca7c5784497b8a50b2fa3dc93fa274567015f7420363e0a13bbd4f82906f36f44718186e0598f996dbd4168aaa00a32ac9ffe7b9fdd5e334baf71ac1a3400d16ad8cde04256d637c421e5c381c4814d710d92379f91ba0537b7daf207f314cdb175b38d23957536cd904871e9f95e2c72fc053e8a4ea0c0276e34b0ca946d5e38a988ddd4859c7a820ab9864c7832d041a867fad80e34947f89e2a9ff0f2c922cfd568a071ab0aaa171951cf60426093a0c756d2fac8f52298dd6b4d9ecf81dd237d930fff2da9bcff9d8c7a3f6e2e50fc24e6e46581da11029150b62bd89e76b74b6aebb5a2fc63e60fca05931a4ab082fc1cb291190c25436bec58b405d36b57e9cd9feea78db08d6ef809348855a081c256b5363fc3227dbe9f0d611902085161f398c2bf6bc3d8767bb7ee973af1ccbeb35f76afc0fb7a268e69644ddd6be6af25f5c15b4df60a40ac82194a13781b4c749c4486e9e1081ea3dbc0fd10fc0e5a22ff43338e23a502b15cdeb4ad0d052f20bdaa4f57e2a5d337228da77e045c28e28fbaf7cc45f4b994f3a51f154c42dff4006db3a467ac24d007ae34c6931ff56e4409c27e8f02fa5cf5029dfda9d722f6fa6a3472729335fe79c6353c8c1800aa6b17832adf3fb3924b3e1085d439f451dc905fc3a631edec9a3260449b89622a138a6b2b7b131e40082fbc5c79c2beaf368a0f50b2fef431ac7acd948d44935213791c52ac930c6c217fe42450e52298cbf7344d0da6e2d8aaa90fcf44ce0b5a039a45edc6eba05d2fba3b36ce73816a9fe42ce528ce5395065e5a23ec31fb76fd5c4446c8d7f68b0c745f1229e2d6e7503732b72a8c58759a937099752768e40bf6e92e466b446c665a16ff582d4fe971f250105ba69c748b46fe658d82f8a3813f875edfc0e468b7c24255bae7c6039d2cd30edfa589a73c513d4e797c9cd7f7b113d922f13d2722d2764d8f5b3a2ee4f8118c08d98b6b97a7ff3162e95c109b08f27ee781a0949e9a829f2840d57bbc3ae3a7670baf5192bda4428e3030219212e98c01485cb0914795d5c52740a5fe368c2ebfe47adaed1e3519bd576be25dcd9ee55e86cf37083b68ecf8d5dfba268c81b4377428f913bf3e4b715f1421b584eca5fb77e993fa4286a3fa2e59c1a3d86544119fd103725d8dc5dd87cf3a4020acbc21a058ffc09fb6ff0ce23cfbf1418fdf09dd959874de2b2e514f117291ca80aa8362e86b61ba7b94ef596baea0ebe2ca910b9a631325c48fe4c8e01fe61ff8069cfac6d9ebc31582e054db1dd5662d19c984842768e11a485735b8e902cfb9c22f9bb80cbe673992866c991f06fcee456f5ce239a6e412b2f8949947e3e208b44a90009b74839c3e79f0799f261461232a427ac740228f5237635e67cbbd3a9f58489d5b3a04e34fcb09d6fb01be3e2e4ab6a8b1cf1fa68d39c2c1b57cab9845d0e3444e82eb4f7c132ad7c0bc1b2db56c92c6c6b52baa908f9344025e1a58bdad6e2fcd9d780197d4757fe46679a26f8f0a979ab8ef49b189c43d9ed11e564315a858861294fa4a4543459606f44518ae1c113265b0d4035de075f693065939e19a90101f3ddd70c8cdfe7ff0779a0ff4da9ec676760b406c6f6cecaf33082fdcfa979e100b1fa6dc903f6b44b39dd6ecc826baf6271c22fbf230c4b34c1672dada5feef8f05ed8b83285a13c5829514a8a1f64be8f091c980a13ac60f0e56685cd1f65b156323c309b5a68d22d94a6baa2ff07625b02b4736ef59ca7bd7c7727a345717aa24d002663c49f12c68d850ee64c065fdd1d246a7c9e9ce87396861efb624236247ed0d5507a839f172e2c3ba6bc3ecde2a84686cd7358a5fd8c9ec29038eeb263076b4350e428de6e75717592cb014699ebcaca7694b7b801c34cab349279cfe24cd418b93ac17219c61026d9f04679c19839d5859939471e1cc4e7329fc30664095fbfe1b80c05734e1f1cda887882f4c1dd04ab8f50dbea199cfa9a2d7a172bf934f90fec84c7e720b8a198c8adbc64ab701b3cd4aa17889d0891ceb00a4232d52f156993688789f61a831f594b46187a26162feddd494ba2ed4b0bd59f0efc70151d6b65a6bd6922b09b517892f21d72ad833fc3587ab798fe30acc6efcb67e20cf641e2ed3d76768ae7d6ce2af249dd430ee251360e52b015f061f396ff0add363435d9f98257c9e5e0b03a0ed260847aa1c991480bb1903c80ebf98a224fd081aa47a8a38eab14d1370ee8236a9ae77fd34c572e7132f5434f8b175fa616bbc9713cad968452212754db4449bfda74e40e6af2c835982670b930f807e6da27d541c20cce0f784ec14f2294d21ce4af92f87fe63feae76be093131e6989dde074bc57ff571b62f925fcff7ba1691b7eb05d796451361f1f2a467402dcc3b09cc8f11d4346a0d7404ae3f7dfb4cd403030b4f2475b00e98e27c9e1d14d8265a48d9c789bf63a4b2d93563d54ae3e0d202eb410beac157dffd5506285f0629bec059c1720279d57ceba3320db79a1ed0f90f7a1bb84661150226a8265f7c6f5e21fcc0dab3bccf2078dd5ba72e8445b10e22d38aa0e29cf23124ce4abed0c47328cf25cf0c84926a920f8956b0f6b1aab716154ee6b0399f63edb28ac79b07322a88089fe61ed8675ad7b7efa5a705e638ba82d529da2a714bf9fdc25dae52209b8953b40594043f93483de75d75db164fa016ba88cf50a92587247e3191bdce5be6c7f8484fea301000ce2c0f43b79e9ef9000e1df4d7d3bc06a9a3ecdee3076528eb68ad874dc83317737e7cbfdfa3ea75146ded884b417cf299b61acb1110e8485b1cc18369ff8d89cb512792c3b7c96ae3f8b20f32c9ba36e16151464d45e266776c3595ec0412c0d1888f41ad7cf14712bf866c12a45adfcea319b2d10c56ea52f6e70e3a755b0b2db7f65e9f268c7911be1d22c2f610290b07cff582e42cf64f23b649ca494ffdaf6382ce96666ba718a13e3a71f7a95da800678ea9e60ca97dbf352af4fec97ca2eb154b850dbc86c3432bffdd6b96f1824521e85f4e5258d5e77836e719e2af4a5ba7dafd916e7f3ea0da184129a21aa5535e70b8dc9fad73683f43f24d3c8f6628052fe5033bb30866c56780b17be9380bcf949882908509936d7ba983042bc3e98822de9a3696cdd3ec9241eceede751191f212b65524d522f88071629856eb369bf7b4f2bfa1eb1c65b5ac6e86125cb670ec8d6900a50f90d31b99b169acad26a9742ffac0d9b1451b4add82fd662c37b63bef292d7fbb62ff12f3aaa2d7d6d2f407aed5bd023bfbf733703c84a5bd59eefbd6779f563ee2e785625446eecbfa83fb12cc29092422968a41d82ac33da81eef76f224bb464e98c23525420c5038cab7b3bfd30ff78fda16e327af080b585e9f03316fe2e51af75e75c9bb0428e66555c973e71856f3b2bbba035a144d98aa5c8aa6cb4bdb599b16627a8dfa9e67971a0c1234a165ffb8b53976a400491e17ce55af65472d7ce81362ec16804f9935672a7e9787f59f039684d5b4304c1eda67e28ea7bb417e25c348d6463eacd5d3100ca942fb1193ea15fe7362a8d1d95f98321f054b14cf2bb59f2cc55e15304a00049b9c3c7605c3062533591898bb9306486227f677d86bf0a2fc06fa37482902d52ab767632735325ce6788025ce42e49217851e98ffd0e014ac4c8c51691422e36db1a95386a0b0d364ddcd7ce0f564d01aeaf6f9c2461f268975001a852d41c8ed0ac07606df78b8b414060dbde2a798615ded17b14495c3010ae725b2f355fe206dab4fa5f2434b49ea3b941188a279aa67d49ba9cf3857396268bf0641c8eaaacd8583deff91f491e351804703d11e89564382f371778dcf2852383b1fc5936ca7adba6177ba16c780f0f178c945bedbe0c87e3778b783b4cbcf22c2a5616d96a23cd3a0386958ca189275d9c372cdfff23af6593f8a329e0f390f753ceed91068f986d09a13e9eee910964180b7c94ab5d61771d23a4ec4606c802444e1857314350c4a5758192201fd5be3ff9ca25437c33cc2f5e5035548d94bb964459dcd98a69a9a40634153615f9dda2078a90dbf9753caf470fc125a62220091c08f5bac1d85a5de8ed2060a2c43ae0fcb3668b1e2a152e964e199a546f36f47214f9672ec0ec1b6b298d598d4bdd049a3b4dd0794bd90424175621859e5892ab7d168641c66cb13abf5d503c24b8387d5c6e4458d8ffede1768a45921e249f4e228e83c5050684f2dc2f426d0f68982aa88dc817d0520e85d4ce4a6b8d3d2ee0cf060f34bfcb71c2174131e6e9faa172f38b14f46acff26f203f9c21aa7434c46d0bb3f551b9d639bb41b52810c91954537badbb53558b99fd6a860b59a5d6c19fb84066354b1e9d27141fe25197c4caa551b4be3b97a854eccf0498970464d9bfed078b7c53168a15c8045bb8ec8a9f6bdaff264d5d588613f2b5fbe6526427d945e9389223540813af44e05a4e76cfcde447ebd71b48c3394a0bc545d6c35153c73a851e9bc4fa95f080c10f433865e6bc8bc49d07d1f802f3995bf41b106c837eff22f112398196d0e813f31e23204c4fea1c600967ae0709c6248c5e513d2c2f0a72de37083d5971cac6877d61c84da48ecf9cf200b11dab699c9b788153806f2ffaf11acf4d23d951941c99ca1b47902ff298523f12d87b2fd85bb82b6f74f912b1a1ebd3ae43700bf9aeab51e86609f63ca8d05ab5458cb3605ace1e1c81552c64b9d0387bcee77ec14f5065a3632434166572642acd57c8689684a196dd987febe746e899d2349299dc4d755f0e213c6d0a82cb43af8fe58940c90673a53a4b079fe88d4d4fe323df12edf4dbb90bec17a0b8eecaf845da08ae18ca83251037fb416c2f504bcfc8f13c8dda584d30490b021b371f28fa9c44a1eeff73c408a1eabddde09681193e77ea061ce711c0b445cd686098bbe6fbcb5c72766e2cd20eee32b448173db4cc012a48fd9655de34c8d7f5d93f59adc579ba6a6c436149e0097db05f3f4dde991e51d8f9dfdc56d724e2b0091972ad158f75ad5c6fcb4c461756c7fbb211b6ce01f9a1888143ba2fa9520c6fc1aae5a5bcd9ebdf6b684ddcaaf5bbf25fa30f1dbc9268fabd2b43207a8de8eb7aff3e4b12e44b1c1e23c065753b2d824920e1ca7e65a1ab1626726673c08a65c03a255daf55e92fae5901a7692b9bf9ac8446ccb0600446baf1faab2d5b13297ce4fa8061a15c88687e1b7f1ec86edd458eca9b77d775512ea4623b72ac0f69919b5cc298401dc465ae46e9da9ed2f498e1acd02b2dcc51b5793e15ac6755b5b7ac27a9e3b34ff9e1636b63b3f0e0b021bfbd0d2a07d5a42ef4982aa4770d1164c2a62c3ccd7689c4f2bfe20db7fa547036b0e717f4888223f7e3516b138d4453337ee82fe53d93fc18c18eacd3d30d9f27b85d6bb4ac6e56b74a86d270629e6240034288de0e4434126a258b2551ae06deaa2d9f2c0da246e029ceb0a79a0465427e1b92e680f1019e77730956e193f629cbf32eac646fa5958fa159aa317d095661016c38a82067b9f086cd2bcf84b4e8f6a678c4d87e86fde22f5f99bc9a9e4b7729dce3b6d193b60a0a9d57331d383a6f0c5ad9cef5eae1d24800e7c635550df8065b514fdc6657367f8c36b5ee2fcdfb9aaa685b5351af2964b3abd2a5ad5b1310220b6a1504cf2064465b2d1a5f1d59e9393e548cafe7eb94c3c05f5081e3125369d4cee740fb3f2596c24d5dd501eb76e058052b198aaf7c9da700495be19aefbd1337578376e68f1340dd5995c336fa3bc82aa1eac04e37c629b66efd1d3de500c3c567ee0a499ffd6f82ca2a25137ca65d0b7f3685e28b56bc5467832fb9aa7cc6aef004ab111d352823f03dabf419e555d6fa0880e37944d9a74e80b7e4ae608cdf67767efd727c0711bab14e104be5a6515846052a51e72803b607f5195f1f78c6c3e389572f519d66430722658f455732945c4a197916754723969672d906fe12ddd7bea9f27858e9dbf8f8686a0242b445a79139e050240caecbe35d78451d848c9d0853d98d40a19799de5fd8558f62e30640ea3c4e4a925bcf6e9956dc0ef8fdf1f7fb2b353054a8ce0c4b24f23ee1d38beb17775f8f2ecc13f214ba975016c817c546ebffbbb2dd9484324fd1a1fa09bf80dedb3f525b9124b5ac1cf7f33e7b28d15aacebdb5a4227314b556e55be806d0a656d2c000e0769c4ba56259e08e65549249ffef3d1f8525e1a6be71f55be6a5498426a74b9b6f3db0306b01216b892b1ecdeccba11b6807f58d0590afb08b3c4f2547b31ba79018b52cba1e321625372c409f1630fbd1dd2b71a1436082aedb529c87b394d94794880a983c7f35994222d289af0dae6ddfdab6591a256e695a4ef5f716a68dd1a0825b0aac735d3de80746d8e3ea73a5de0f19fb844010f6fd065c254a8c6a0798bafd363904f51d24b82c9700fe2ab5cb2136a4f64108a5d02534c099e1ce5a8f04c01db1226d6a530a2e8926eb9ec7f9d138827548c7c6a148e1ee2770811116f77a436b6042ad3102b8fa87a59f899e894a3896e96cf8143edb7cf0f06b47009adb3ddb7c20647bc6553ddfe8638bd60a02825f97ba311c20c010a739eec4b39336a30fa42c81128ab753c5ce5193d9cb9970678b0736504907f6adfe41d070987aef29f01f81fbe699131e5cb8d330f32343d65225c892e1622a0ed90744c76f1fa859d79a9e2d62111534009fbdedfb352c1989beb962848f04e3f44239c0323604e4bf25eaaf4ae17482169aca52de32c05de72df63f5e65534272006037ae694472ee514c071430bd17047aba84fe9341f8ca35e2133436668ad37e6e38201403ed3aa5df3edde1a296483f48d999512f4d90b2638596d2e3719aaf08f74d01799fcbac1451b52f44fdf2c68a7a2eda76b670bac4525dda2cf2e4d4bb256e94be2bb04cd261ced9ea5f3550f0046be2ccb950f9de2dfc2f912b1f543c8e186e53b774d3413c2ac47133f1d3f285cf4bfa5bbbfeb22cd14a2ddb7e3659b54c6773f63319de05caea8dbe3bfdca2b98ee48ae874e158c8fa447bf36552849249414170aa6aaf8c95bd4a74fdae06731be63481968741bbb8f95c5adf0561afa88483ae82fb3e327e034b9f0f6be804202a5bb6c7ee26b8bd1ae622f39610d246257459a290c116e6b321b24acd2300c2e817b7e80296cd1b083a9e65307ea01d2711283ec964d2b31146e09b180092b116663e6398711e8695d9c7d1d888e34671595ec01c2c9a05ac2137b5844c65256ac3290862faf0805e67180accb3241cdf90b696a029bdba03d4f37d8048b7538a1667222ef5d77fcf2028d3cd08fcbc32ae82f1198b5e30ed585e9493bd366d1fd5bd9796445f4b130e458cd476b3155571aebb16798667c50e6e702c97993015d2498104dc5e9ef9bf0b1e92f5dc63457fa4c701dc1e261d50c51e9071cb32ad96764eca313a230a4ba443f7e8e7559d485d117363777ba6f08457dc04a008c85e0126f75bb4257c1a70d04411fddb68fc41a4a813256d9c8c383f1be1048572acd4239bfb3d9a9ea055ce5efb5d9dfce72eb488d0f9c0587349fe1e60429bc1d4fdea331dea8ce1256f6ccaea7eec7fc8620c55d6fa02149678273efb99fc408959a60e5da391dfb89c4c55fa09fa51c294fd2e1b5d1450f2ed370b4d48be8ad2132c54d52ea13eb31702246cc2f6febc932184a9fa2dd4533c1911f2998b4faff3ee759ec95f062d774f3c77a824424577784ae74e7c7091b574534a72d6e1cf2546b1886b84defee12af46391541efd64a99fe3316d7bdc0c4cb55bb90493ed803fb06ac6a1c1247c97c328cb7dc3dbfb35d04222d7808253a55a75535cf74a2422693d5949ae3eaeabc736f8c8dd100f711eeca5643846a11bc330dfc156c2373e520e8a06774962c62a7a627b27c8a123883d03cce1e0b94137bea63b4edb1da434c735533191585dbb43dd42ea86a43eef331ab6c871d2743c198bd3510cda4301d2697a7f6e693aaeb377944951ae083cb8b5553b669b04bd99880d412aa606540193c5a2d2f2f41bc74ebe94d98d7e9e8feef6888a6fdeb896ec00905e995f684c69545d70f6c45ff09c486be7d35b3e10dc4041c51666769c580188150a72a95d02611f5c1bb58d3798a7ad115c79408e0065d666d857552ce6861cd1e6818babaad7793d44a9c9a3695efa745384508a80a819d0ae6f1b4a4a9e410c170f2081ea361fe508c2a445121006f5a44ead51abccbb39a058a9b34a9a7fecb5c1808efc508da2bc5940a00e1b56db8b5b67f576b2edfcc7e22ea05e7f075df39f33fb05ee3b81a5f9247fa8bf14fccafd8cdf5ec40763e4a69396427986afdb65d3fbcbad203f117eef57791800ed4b0aa8f7290bed80e6fca2a4a69165953eb48495b4b9336d8d9e05a327594bc71d06324dcf393daba4185ff5b12e55d988fc59100430782d3702d254caece585ea0ed4218b1333a36b7380262038e83755ac8623bbdf2a4468e932a9ea552be234826fe60e74ae34614a8b55ee60a3fc0c238d98416b2a28a0f98112c50624260f7c1950330d91bacd76daa59a88f7130b9b14abe375bb655bb2e59e58a90664738ab10a74a10b76d90a380c4eb7b48448242397f2650e070a6022dcc772baa11308046c200be6622edcd0bc8ebaadb7d956cb20c249ce3cf72caa635ad1ea976ffd2d73437ca1848ee89b56fc89e6703a946fe7e65ae6a023f5cbcaa4552c824c29157fd8c5cd88feec2cda2543d79efc664b53e9c4ccadd23eb683f0e4d97e60cac1d38acf2cfb22b918c9ce8f6304df7a11fef09fc15659037576768a6d95f97165ce4f1f6c5e231f75ee9a65d0edef71bfd6d782c56fcc8362273498221cee4d41230cdb0785eee78433fa0dfd710aea4d4d692819c822334a21a6a0492db5923be6988be3d43e14c32ca89149698d86bffe9e7fc74039523bf9f782f2b6c7fb3752ccba9cd8c837d1ae0f655c83d2d45575c7b814fd9e7a456916f28f5e8a4a342b714e8eb4ebcfd320ab3476f8d9a2092cc2d1124cf57551140b386fd28c0dc02dd16c090572e4b42e02abe6e10596de99a39beb5824eb73580bef09cd12484ac50531902112abd51ebf8fe1fa2121fc2548c270f3829c776bb40d2424f383968d3b29e2685c41bce9d9f1c721d49e48b3a1dafcb4405b0765c98ff15377d47fbfb7e307f9b4b8f2525685d2de399d7fa44b84fa56b5c772b34cb23c085fa9a7837c40a009dc923cda14a9fb713c9ecc3ea556fadb226f759dfa88ef7e063c92987b5a454a1fb0d809832716381f3292d42488834d45111c7997274adeb02e3ec6d1c8b98b3b40afeb4646fc473ec37719358b51f0f6011c5f73ad69fcb8f73c4e53fa1216c890c0aff2db8d0b360680b8a9f98aa4d4a8586f2fd7f4370b6a975c0940656db3f037371a8141dfa6364a5dfaa294347fafac4323b739290cda8d33a7caf236b2f97450c3821ebc46a561e41b32d9ce821c4e8ffdc2de8479ba193a3731dcc775b2017ba90c9b10749228dfe363bbf83261cb0905f4dd6d5afb01cad452992189e429e5fa731e362734aead5320acdc493d85c6534c950f8a3ec41f6bda00c5a53521a5b140fd0afc6f545fb9badb5180dc9c4f5d00b5960ecff1fb4aee5b6720b590509f0ff43fa764921d5fbb4d639cc9284c26e9f37ea37ea6ab09bd0a648c6ecd2991c0a45a0da0389d34da131f5dd91d716fe6740c756d809eccb652fafc2bb029911e3b47fc3452b7918ba99c7aae78e1adf7efa8dba529ceef7d6d241c7c8801d349f10a618204b3501929cd520bb601e50ec12162c649b10d4f98b7d86cb563cbd99890d08bc93e05905c69f590a57e130103f3771e3ca709bf0e918173c144a76956ea2f67313c2888ba4e0dc1d34d85520ddb895fc0c7352774f8039d709a2afffb2e0f866038973f02ed72d34802782acb5827adcbd16e4124b2fbb4a1e331c88ba8f8ebc2aac3ec1ca1b4b0c05b42146d17734badcf7aca9d5d8e3e792d5ca83c9e8f7c33d02263562da5ae98ad625405435d9fc45d2d08ed01f377edeaeb9da2e89dc9d146b6f551d8c22980a3b5ef57804a7241cb42af4a705f60e6f7535bace93a212471247e497638919d2741bed05a34b4945b8081db767dbda6ff773fa8f1df915bff8aa9754e25501bebdb055f9d8b9b611466515b4a5fcf507fb523401726e706dc31ed49939c7a08350b8389a1abb3cc62ee023abe7999e27317101393c242a562b2a8ed7efaca31c1f72ee71bbf29c5478ce6a1ecebd9b130437fff2e1490348d157d56cbb1b1f8bb940fc0a42cf32f69bc3ed5f7ea7bff6bea0a63a8c9177a13a619f0da1568aa4c2e3f78a54d5ecef307549c872539f37152d8d6c854072a11d55acc5c92ebcd7e360f1c2539ac31fddc198c4b9cf9b36108b31b3d8d16212166718d57aec1762848c0c6428a44e555f5b04a7b55b68019c2cbade2a57b2a8141903e2ce9967dcdbd3d19a90a697f526a1c4fe0a7661aa589eecca29f9b45c3e5226a330b7a20ddc9e95d6046446612c5cf9657a7d2d58073d7a56e2cec6136e8244ba10874198d6b8ec05b0d25b6128a05a471d306223494d7161605268caba884140477f9a3b41cf20052439001ab15c12f967eedf6496372702beaf383e306eef5507cf1dcecdf0e599b776cf84156f17f59f361d784292c07b8c8379ba5234fd539b1e77dc9e4471acec99a092f86eb39c8cb2b0392d94a30ee5a89a01ee1fc78dfccfb1e7e84c186012045c62edd53808f6db7143add3ba66f64430fd9b80b8247b33b935bdc5a282bdc3d25b90f8582f4c0aef469b1faf0e9c1e748bc26768090480b56db2ea750a7b0b3f4bca3160447744ef78b18706ed80ed4f5a21930111fc740c3e05faf10c33c343dd91d2891e228f7d90c82c9d7019ab702333580b5e3dfad8d291b8aa54e8755c52d4c7fc44311ceb801e30cf5866f462ec6a10a83bf983630ee8d9e3d368b797ff5642564b58cffda8637809d7fab3b42eaab44f244bbb64f897e7693ec6bfcb0c6f37152ee2cdda0e4ac56da8ba28c1eca46b975a75a64bd0735dbc55135ef518703bee93fc4f7472213316b7659fcafb9f366dca1eec864ac3d38d10c7a5ff2895244195eebeb72dff70775ce6b38cd823a0f3373800bec3e29878e0aa63df32e6c6c0c608fc15c79ce7f2fc789082bdee32e8b2358b2992db6d63fe7a6d5a7c56d821087b02d87e9115ef520e6fde6375755ac35a714d0ac63ae020e6ca69984e0c0610fd43670876a5930eaf654fb674c6c2a41092c46266ba17cef6f21d1fd1ebb6c86042870776ab1f7046fdf639fab2a2fb006d8ac5f164fb3d523aecf59ffe3a60fa01a4c66d9cad2ef2e39c8e724b7ba9176bd18779df3db68c2b24a10aaee22cf2d16e6374e09758c910cc92d356cc974c7f22bb82a4701d1a99db1dc348edac906c7992fc757923cb1560dc52ad0e27a2b5ec2f339d2b9f7a77cf75649e85023549277c3440c987317566cc383260ef9bff14b0aa1ccae01880b7c8e0f74d0898fa3411682a712da966747d75548290da414221e716bcb797d19abaf916e14ba8e0a800ed91ace7bb7a66d6534599d386b8ace98c21985a8d0d3864db24710c75e4ce4064a46b7141edaadb96f10ac80f389367ae5b86ee0c10211ff3e5ca176ae9109d48264b3605ec6e974ac7631f4bb76cdda6af5efa657180befe2ec75739fe6829bd3658908c7c6b4d7540be2a1ec507329a6414a9101a32b23516551cf7a2b2d8c88b8ab10d6c2973680a7b3c70c2bbd689ee0153d1d2a5962124117ccada7bef907d9342304cebce60947c6c031a818280945cfd165c016817e710b3bf0edeab146533c21f52ab31f861a71049f51ea55f4571bbec581fbe5af42accff601da6893ae7825ab6e028e537671e5c0ad99b8dfa51647d702434fc219ba82f73a0ad142c7cd13459587b9cf8cf1f5ab46a34f6cff66207cd3afaf78340df8b4cf5bb0a5f3d4683815b8976274d51e53065d0e5345dfb14455397c1b82c9f2aa88166b581ea7c5d2574ea769dda343e9f625ee0b47045c7f3a8f92c7cb9860a345270e22434e40bb70d1d12bef9127a3766ccdcd29aab05b34af0ef33c661d49518a3a1f7cdbfa51317a590ec5594b00701f142452301bec1f491691a7148cc767e2f5dac963bb542b87d01d78a6f709f7b1877edabf588905d26d277f1ffc58469426dbe2adb6f5f9c528817158c5abbb456c528c7f45d418ecf7ee2c4387f69000d94507d06a0e91079e25b08ab97d6820f51c5b370200092022d18fac6e7c99c5cfbda0efc61c6c28b03ffc8cfcc4d1dc5ff15b114a3113014b75e8ef95dd7018472d45739e35a56f778440841d67a4703248140fa201a95e26d8b86f2467868a2f80c8d0313d743aa70d10d61d65e9097e1ae7e33138e49af44999be2791afbc6081f863e754cede1e8f23e957dcae516127d0802caec64cbb0aee3b633cf4942bf2e54643787827270ed2dcd3342324028dd3662ee17ea18075a26c23119d87d519516da2ec64087a97e6176f75b0d61247d264de0b2cd5150fa11ec0ed0350af10cb1b32cddca6bf56ee3f5724fce44b570319b86b61290aedf3c71fa430b8cccdce1d0fb3cf99894e1904455db8bbb27d8b687546f076f6ea366a920d3d99950f642a56fb1ff5b49553aea82d2710b1423e90afc716560af5edffefcf373c23ee5564036a4b90db19b4c1e3e1a545d856c73b52ebeea15a67a1c4304bae99ead8fb2332b20862b85d48757566923ffdcded6e800f8b0731667166a67cabbfc40249e38a83c602e80813c8868a36a29294c87f00c340e621390bd755b6c3c80f426c2294b8179f8bf4702fb100c9026785ed6ef434d72a3702305006a7ed8e971252b44ac39ea2960f12fe7b8f78783f7e437854fbd28a1c30d913f8bace2b0a8768296fc5bd2237e2a198cb9ed01d79acc00116f4d6cbd2f0aecf9b22f77315081192ec0fe327548e3f51718f4132330cb6f54a4a2cfed405869bca8c11b7c4455dd17796d2af45709379a6603be83654e9a5d06450353fd1f908fb6ca6908d508cd2d74df1af0df6aa21baf0ab2b791128c79dceace3600107540f8fa9abf18227b1249e8faf571ee43abd3c4290182786fd3b03c8102814b99b32ab0caf614a73be6f5ded5871d550afa19d702a9577811ac0aae82bb085a94e543b5d8865b9db31a077f112deb2e0efe90eaac7a1e2b92a57be0ba5180cd468937937513a4d1182874dc6b723066cc4f192f115659b462e17de10eacfead454487df7ead6436e1f6a9c997e99ba5d0f2744e85e096e81760276ea4951c182f4908c3b5b85a74cce81d6d936c5c179f64d6a5391164dd70d20abe0bfe2c9fd1a240080b2f5eb3071a39cac41fb6ba786d2c11b58b2ab7e4c8b92524f73cc77261e3d111b8e442fd921fb778867b5c843fde539cfe7b70097ab2b7e42c7399818be7c1aa2978edfa3b689eb9ead37f90a746d502c23838071660d3d93d6ba8e00dc8da0dd6049f769ac6308763021211dca4254521d0e41c0193629bfe7e9bb109b468751d3bc2737c9e659922bccfcab01205604cc9e9af5bcf2e4de9e38819377d7a01402132a8cb71b9839f7b838c4302b18570bb7d3c104377d205ec9cb9b991eb436362105422775be8bb75b9f96b166d1214b999911cc501d81c154726a9b13439df1d0b34c89e9d38ec2e3dbc0c662abb68c935e531ee621696b9bdf7e6ab6234864da0b0e5bf04123a4e13ec479f1ffc3da38969cb18cc9fcb8a95538a67498ed62920a83037ab3df36acbf44bcf5f6ed86c388fcdef7e83808771748feb0a7ff2dcb1e939d021616ae3b481692a0aa2b88f71a71f1078e5c2d3e1a8c235dc692f3a164d18fec53764ab611d551008674fb9d790a4b0444c91df6216499baccf46904664c8ed2b2aa4dcf5d89ea879a25317c04f4e43442a244d6abef87944f163a299e1277216f3d0b52bffe67db4acc5802f3e9f22e3f8136731af84f82aea3fe26fcf11b3ce1f9e99d03585a6b33d601c2b773801b42a219e6b15bdce9ece66f899bb17664c5b86fc1aa136d88a7b16738979e089b7deab80a725c04eca197084b926491da2e215efe5b7786dea342f7e0ed79143b280882ab9ada097102609b715d2454d02fa6a3ef628815162f97db91f77f2839a76460ebf0c4251bc97b27dc683a5b94ef1c46a7b767858442afc4a0d9e3bb3143af5a4afd64d88fba740fb3574b5ee51078cec0551b1a167f9cfb600189395c747facc8e514d0969df4aa91bb276fe5d8c8a3643cc326b78045947e7093dfb0098b367904c5cdc7109325221e7f4eb06819c225c92db44994e57d3dae4c4925920ccba4b28bfab94983e76065863c79689dab51809341172a3945a52917c1ee84b954c4def1c75a53d157312b889782bcf41049d96cec5045a79cb90e0286436fb5dba958c848d345e140804437af059c3308f443cf813ce58b6c9c3958a02450d252a05d2e2e868296968b19d0fc190d546fae4b6a02a2481b31f2bbdeb5250e5c91cfadacd5d79667c8693d2c4e66ad2929742957617f99296329ccf9982723a77bd57958812ddc5bfee3486a2f436e9711699f40ce6245b85e67af11deac3b402783f4c874b3d63086d2111e8131fc99bbec9acdd7445007c84e1e10af1d8b035f1ef1c489f4a5e08c1c7ded7f7058dd3b56a063357f75ac7ce02e3cdff8e0d324f9e8b4029d2f388ef86fb01258a9cb054a75a5a07c8e7ef87109fd96b5c11b28db27f780544f7077ba424a7427ae6bc819edf29e566e93e1a13432405f0d99557798ed8cdb16a02e23befd4766e8d6c8267b73d568813f489c3069577d37d688f9e7dc339702b88fd49469d5dd71cc47f5ba6762c723491c0fdb92859267846315c4e5218c7c6813d465860842893bc4f55827138b93882d1661f02fedf0bb95ef81d76c43da693b2363876ada13ebc98380c1d757c15e8822cbf2320a4e45b2d55274df7c8947071aa198d3a28afdecf4f204db59a007566a710f15400f646357c920e89a642cb887bed1d26509bd9e8d2e68049d9635838c14b543ab88bd93c21f7e2fc7fa71f8042ff516a0529d72c0e97b3f590b19e47ccc0d5069b0606c8b92bc481372114e3e844ddeb1cc351a0f5b1332a269c78198dd6b770ba2ba658f1a040b761c89368ba7ab4cff686d53159cd6f92ec7f3435575b80f0e22e4e3a76e684078db4f187c21a5d9c3cb299a15bed6301c619427feeeeba97b730a897bc255a1d0d6d1019c866d48a505f21985c79616ce5543174ae385367def5f3b875bcfd6870177d0ba78ad56eaaadf157c36b2dbfde704d10f0dd7cd804b48ecd2867b01d22cd0c195ca46dbd8e54554d8023df07e042f1dbd0b321d5d05c55534c41627b676bc5170de728b8fd8953187f76e8b2e8bbe296ba1001c5078b0f60a5b93c52060eca6357c2b4557eadfd638162d7ca59d74f6f0bc778675f5a4cf8ed045d212a74cd75b207824253b46d76796541e53ebe3b5e06d3ec326299e27e7a690b4a35508939fe59a3da4b89d31f81cfb05ff91c0c5fdd6693ceb65d07d8455bb034bddf26961052e941dbfb64d0a8b77316f818b70b5675ca7ad2e34e41d59a2a5157292923209c8d3b926c79b99a32201e94a3168b6485d8eaab95fd60880c07fe920c2628318b102a406b8226985e5d2678b806f75f6c43ef0ab723890dd63a5a073de5f78e51f961a72e2e55aef77f342bea74229cb10023187e152f26990271099d983bea4ad51fbdbfc930ba4a8d82e2d5d6dc2f8ac6e8bb70542148c6e1cb75b1e4692b51272e62169689212bb100b7fc1ab0cab1e4f51f09e739c86bf3e6e08fb599ad06b5f2db4dec3bf33150449aa6cd7e740565eeef98bc5cf91621992f3caa6b863f9ea57ba5f043f75d291569afc2d6efe8381176a13bc2158873ab4a4b915526840a293f7638aea0e7d92e4648440f0387690b55eb842dd9e0bcc1a1788e5ad942191a2963443d0c068e941146e3e21c7fdbf197d33d740dc81f62108be7aace4732c397c8d6edeac9b303439ab84008dba7691b0a465482f607795673ec3737f626e7df5695ef21a9e225211b8931f2fd6f6bd1ec179a55458df83438a62183cc2fee1763e953bf3d876d2832333f6c124f8076b35f30cfa57cc7712c419675020d11d1f7ffa2d58c8cbfbd2c88a7a256f8de523900365371f2ca36ed53c1d0d56e48379fa556bd180e85f522ea20cd12576da6c0e0d45861907bad20e182bfb7e911bedc8c75f5386132dafce0146a29d6cddfb1fe63ebf7cb9aef22c95bf29425f2f777475d3be0bd8262dd581773292e1381a0e1fdfe2d52928ea5ec4cfbe6a2cf71677b4fa983c0d0019c080bda12bc099e34f4bb488bc4f01b818076e4ba8c9a5cc3927c602645257cdc87ce66bbf0bb25257916fa48f2dd2b330c9ff49027cdf5cb08342ff189041db1c8a10a9a04ba88925cd9c34278f52b1d74a0ef7a7f9531effcefaf439b38512393fd8494603b293290865c6d87f0dcd8f0959f0aca28a08c01aaeb951f3165439757d30cdade99103ea12c28b13701c29ee3a733f83381e0f539a8ad3dd0c800cb26f050e73a4bbbaafed39e9dab144d3fbfa69a8d2d3f0c6ce09ed590418f4b977a70a4f38e7e6640987a43a5f1ce6e745d8d5634d4cd8fd56e2eb0aca4592231f9aadbea5b6a8886a75889c11db2a63895f1dda2bad87ebbe994c14fabcf5bff98248ea51d60bb99b0ec64f295289d773502c68972b7ffc80a71aa3fe23ef947b39df2a41d6106c0ffef4cc4969beeebbcf2b04709253d4eb3c135ae5b254b21c367f367c42ca2d67365d3fd68e1d6f9ae3f3fbb350571e6cd4ca89aad36e93e02e1dff016ed36cc63b690aa19ab310dcf0d682e4a9dab551bfc58e91ffcf420aaf08cba239ca26d075a376fd11ea8fa118fb2f5f9e39984ba41b87db17fff13146e9a32687a8da2c31ff3bddf904a108a36bd4afa0ab054e7eb78bcebb69f625e0b8e0af715bacaa4107d78b0d5e5da130559f24efeb8bbf58c024f743e4d75dbe31b5aae4343d7109d0ebf5d72e1d01ede3e4b6645fdeadb74993b37881588ebf78f24cefefb4df455087d0fd62432b37567c3a0a4aa7353a4773ef42369d84ec3d23b6a9c7530a5644dc0a748a719babc21a5bba574325c59ab70aeddb2773d3baa184236f990b19e0edb918696bbd7e4dff9826044972efce228374aa83401b9da69bf255a520bd83e350aa07b135d0c2b325c2362be07de7a719827d44f5caf96ec438585ed5f4ae7c6d2ae807b5eba1c83200a51eb9e4881b8637fcd8237aeaaca90ff4a1a9832466a8d6779c0abf885f9e8c2e9dd53ddf2141d51a58dbcadb46c9df4a43588042b9d5d5cbd9fea47dd4937086c061faa0154a270b03fad0ed44e89be2073ede80f9f5236c8f35c0473c854eafd2b6669242a4c6b3402ec826a6a8eb2b1a69842415f11087e413764fb9162d1e2d5045a36c3869f4c32fa7cd984d9d78047b55078ada062a3a0284d217297075b8e62195bd087ea9f55b23bad01177e0dd9de542a5355c1d07144724fa948d738a344f02139b2e947a9f033c1d69d94135ffc209ae0d3592d34741858c68e6ad96d3c1eedc9ca7ef0d1d91ff91b2aec8bb1387d608d8054685e10f4f89562f025a7107b2ae017c03ebb0d153fa5762f305e8ff42e0a2de7180e3ed8095956e9a1e550772801f655201ad8596df2c5871276dd545ae8f446e1ec8271ee503634d974e58dfe901fd485bd4f4ee9d19c50e9eca763deffef9eab511859ac9da863702e7fcf5cb5e6afbba93d51b5e59ae8603775c7d11bab96671130a5e6e7c8eff85855c7290e88b5ac79a3b048ef4126b17077fed1bd5326a0908747079666842a150d7829fb74b4a8f42b65654914983d53ed7f62bcee97876b1e561fff31da9ac6458341f9e0ee13bf971cf77a9b55de122ef53b52f6c968353e32d55ae58599691f08de09e90177eea2e377348fb1a745de01dabb23e6873d590763d226c205fa4235bdbfb5c6e608065d2fd1b6b8e5b4a0cd14ff92c66f2289e9d687e7572fcca60e4a00247159654cb0137d5aae42ff1e48077d0c561027d9fc1e68fbd1f820beddec814a33da65706d8927cabd19d5c0bc2bb98e1311f43f7207e1686f68b2baa9bf9776c246f4e9729a487235a4329deef890fb61139d11f1894a2ade1b70dbb8ed99bda7db7e203af3242edc369ee075e67984f0e18a71b19a7d67251f4bef739b11e21fd631de02dbaa0a79fd0d058ce07ec2db12b36d9ad5a86d69d3678d43fa25f993ae19bca622f92b07bd60e69964716d7c68fb155b8ffc278a10062d363bcf77bbe8e6a5cae67cd7f2320d029535861978213c3b9244ed86ac50f0e3498c1af9575bc9cfd7efdead9b21c77dc3beb7b11ce83ac0411ed02fb29a1e38e5b094b4e83d4fa1d79802e33ab758fc09e1f6badb57c592f2638df16b70cd18083e20e905b0b5c01fef74cafba187ca0acb65b2cc6e1737d09fe6d99ce32487d698a3dc9880b124ebf03cb8c380ed1e537a8f78c756cb78df777c8bd13743bbe2cabd197685e33b49f8c24d754f4cb7df66576752637d6c026a4d188a2b7d6ae2fe387cda4fc843f5b1a2bfdfefb1066bed5e76c9dbfd4d35341075aed6085573e9e20b3e7000ba46e0eb3ca675f3e007d25c5975684ec91cfba177e3029daa4b8b3b0f1086bfebfc73d89dcc37d2ee0e5f07d452c0fae289d31b1a52b826ff907813810e5976e7ae5ed389a83908cc8195816d8e2ccba5d1df1cfd4856c4c92370ae4c49d533a28aac343a56787900d1f00baadd2a9f71e2090d65c5cabf542d0eecc7e1a1e40b5898d04a04f81bfbc0a2465c409becd2293668549eeb2a34889216500ff1a613280dc8f8571e4a5341a93f061c9ef754c3a5eb6c6f63f872263a6153bb1bc33aab4770ff18b41b0935c679cb5cbf0a56986264a9cf2c3e110be41fe4f8990f16db6f1e7775a31990f9e0fb3b6ea2765717d16c62eeb412134602965b579f94eb992d40cb422111df3c963d350a3a3d55441c0a519a05070f17265bfc18f1c0effd614639e7643c69359d593c95886e379629c2601a47f8207d172dbc952f2fbea4a0dbcde35663973766d841940af814a2fa3c3f8d0e64db40652323ffe14d28d2f048cdedd15fccc9733acb725f6654a112f435618c01a906ea23c69e2c00b5b6e59f7c722129385bcf92ac81970375ce7824d79177f789258304009c30f4174ab5f93a292b9f8a6fbce0e62d882d0e40a3664d1a4f365ae1eee1dcf5561656eb16688b06906a1e7db6ba1294e3a14ab4d33b84f2dfe500d8a641953b791b602d02fea693bf2585ed2c77731d3cb60f5611a7e0a8fde83e04ffbab5c6c4247371beb06e6964b800681bdf6d4a302f339d8e1b4fc9e91b4a9a2723f6a5d5e909f3037bfe0246da4db4fb546c6e706b61392c5411b40b53c95522754321d8ee138e542009370c30597ebbaa85bdf4ecf0e099b67b7e2ffe7c1bb7da494e769106d5f0efe6e7e256086d8634c4c59b92ef2f24a3ca7268654f027118be4c58b673f14406dd86c4d5db82674e43c2d9f3f5fd20d4b82ac1bc190fa87e57a4a8dcfddde94b527bfa1563b45f45e4392b97b843bb086cfa694896f7d7b3a2db87c58f28bbcc22e138f43c3f2fd25a4304322b94e0497d04cb81a2f401bbb48133de07d79fb0ec4b90f978b7e94944b2d6b815d47ebc6dc5fb14a58d317a8f94c8bcdf83a9c565d8383e2faa884070fc57ed78f95f66a229a3311ac2be673b5f5f4849541d7a67b76d34b0fea04a18aa32da7a855c489666c190dcf208df4ee2477afdf30a45e4db1e45c6882e929fb8d99da594a484ed911e850472462b9d409419e5be222ba5c0f19443e1928df84e46b531fe75c681a9401e9c35cd989f11dfefe20b3a4c7b4cc2fb98a00a921c45f50d6403ab766bad8607c4fc30a8d236d05a6109b93bffb764d13c672e11018452d0733d816a315f6b211b293907b7293dc7855fb3e6df31ee3d7db6c4a3ca3ea10381a4c03e132ac8deb0c092731679252ed20981eb4b2b5c0efb7ce9341f8a54b2cd92536d4fcd0962cf93bb6b97ea948465e856272026b09ed0d245901ea74e93ee05fe0a15f8b755ce1f6515a6f81697353ae59b862952fd23a84425522a13212e49eccad91720431d23c1f903810f956fcf46224a28eade04790723f6af210325c1fbd9f968b7a1da58fac3b679880eb0f8036bb935f81ceae2f0b679af3d6ac588315053caf095a5558c5c9a625df031e17245937718b9e0d712c6a1b8c45b692175d279c7c3afa7559bf7e525dfd465c958adb4343e0cf9e8cff64c9e7420fba08d2fdb0ee393d25628dabe8415897032d2b1f93d184d5678e3f6f113c9d586b315f279720a0a7c47fe6685fdbc5836aaa7c6a9ff0eb8b0d6d383c9c0e10081af546cc01abe3ee9f45e6089b1e694c3b43fed0a0a74edea68a8b5e49f13cabe2c75cfc2fe812384b05d93b4344ab7e8b9160f7e9f096c13e5a5857cea325e22abf95dcf09843ab09e9184def7f275626fb35044036955a04047f22f1ae19f3f7b6d0a0fb213fe94ac455e24b0b471bfed2aceef77fce1ee11a29de8a396389ba3d643f5df6107a6d8a8e79f3b5cd779b858b84206b39465c4e89811909afed2143b1f66e624559fc7c30020a5e6c567a5d2a98268d613c693d62cc7be83626c7de4886b8bea3114be491af72fb762bfabe6af8b01e051037c00e6f7634fbb75a3c2b64a573d98e43c352a413ea62111e3cf04ca07d2bf5ff9c25c7805bcc0e8c2852612b04b182b4f86760db5a62bd256fdc05db1b85de38b9d67ee26e31389e1cbf651c83e0d1dc35be6dbae160203659c8dc718992437c7a4579668ff65ce247b84967686203e60b451972aa9259b3f4d9362907b87f178351e05e94a123c81af4282888724189c64373bdef0db6ba007ed027905268b06a955f2444d3d7ed7e861c9ee37ed097fef142943b28b3c7c4cb8252708b81f73913f6ae1f084130b5c83149be3b0bc0ec9fbb165b4ec01437e8885d9ee397574f61a66d09b5c227ae6b492a5d2fd2eec4648fdd4b1b67918ecf170facd9c94ba28aad7e6595e4ca9b3b0eedaa6388154f091b2480539c57085bb38cad6df605f736408d61d6db4fce7cbe8a05a92966459070a8692568068b5f2213300de977d494e9c6e9a7837960ac5473605002380a9bced8ca50e403d0e2ebe2b41d717efc6ba5450c699e09a59edce45414858759b63f3c745163c2e3090cfa5e7d562b3940976a91036877198d9b30063e328790176a7e7606f60ddbee87d555543fa665ead1fe71749b4c895560720c347f9dc886596797a60fdf82f11063a3213ecd540eef3b946e1bd8158116b36e5c28589b2e8e46e3ab001d2afc63740e25b2e601f2ecb839d7483376d72df0bfb277d54e2f0aa840df7e72fe7ba5fb49d20431f926542e9a230e2cc2271baa05cd2eb27ec76fe9fd8e95ad3321715abe7c40a62ece3f1b08bce245fe4430d6ec5e180b6413bcde8e05ed3313c9380cb333ac15d26ce4e734659d30d844716bb380e137b4262632a16310cff16adf0c8c88d8f9b8c77399b0fd88b3c09414713d307bbfdb9e6542ee7bf548eb771230fd1f1ce1b94c56f2ac4a1a7e62bdca60f685416b57826bf8b5d57215dde5eff7eac37edce4212bd33d478faee34e3c46f3a9e21e3ce77df7584d95879c0eda32ff5a8adad9a2b4077503c068bd1afc2f84dbd6625a7e71db2afc182e2718b206bb5b9c92d5d77e0080375290f79fec2d4f08b381c2d33dd4ec9db5fad474fb9d40f927b17b89b71c407260f5d71fdef78cae847b386f2f6bc8ef8f9fd9720b78490b37ba235771d114b91d9f326c0b3789233d24f3737b9bd88e16bd179a732d92938f88e7e4a33044dd323213d2a794e853818b415656fdba92c7101728be7a19b14e03dcef501d2cd9d227a95a15107235dbd937ab55cf445fa70ba78fac047aaf1232773b681f23a5bd3ab759aaa1622b21ddaa5cdc25c3dc81eb76b27f0cdbb83ab8b5dd63a62b32a79bd6bcd875f6b120a6717eb9ef819e72a35faa62796829d5da7eed68b6767c9c78454f100bd015dd54ae4c737157d670f2cb0f5f2af632c227ba222ffcda68c98347bda0f5b6868fe4c49b2bde4f94020f1e74866257961b1bf943ad745d0154c69016dbbd3b2af356674fe3dccb92d1486f9750badb4cbfc6324e9a7a08721024379555e2f00fcd15e8dcc165c83fb430eaafacde9bacb62b17c2957c1acafb9594aa5cdee8077f51a7327ba1c26798881b2e5d7b5d31fbcd5c41a78a4b9f20b748f35213219cd08324bbeae10220bbce121e70568726d4f9a38dd8c46d6b0ebf8eb1eb5e48769a40c6bcb1319dc46f03460c11578a36e741f5830230ce6935c772f09e115f806ac2a9d57a9e4443b181d80d41405907e0907196af90798b5659bc359f8907d3c3605d0dd4eb4b3ea3c4b04bafdcd384eb7a34f6af74b2ba31e0ccee3fc0d554ed185c6a8d21be7c9677c980d66da6cebfa8642fb40b68ed4a53819e485303466732eb41c913600c634adb869f2f928f3c9570b210abbfc74ed882ad8ff8ffeb9485b4c7511641a3fc4310837c80eb8a4de0649ec3b9a9ea973119c265c93fdcaee47af3b4075a07ba19323875a108b973af63405a033ad9d15dc29881cc8456a5329307186378b0f2e9f22e98767e78ab5cc1bfaabb7c511339f60b218845d2f78a746da6a18b6b2c598a4dc2a11acdeaa1afc983e0ce7ccbae4ca60bc7297271a258986599a97b3d97d4df2883c60f25cd7befe4a3dd8995028f4f42976d918022d2021182ebf22176e5bcf5f87222154c534105239225ff0f8558400ad970b73b03b5de98951df5538e03668633b842d9d739379aee283f8a6684f756319ca1981b4fbe2dae5b0ba1c40fd7f7b71500253d348af3a759f2c610dbfaac9216f7643c413c396d832f1dc50693ba41d8253a56fb31d591abf750bcff814e83db393bffaf5b1a6a219a6df241c6444bd46baa7d7d026354dc9890db4d0d99ae1829d45accfe013bec0728325e8370cb51699b9776f24ef6a624be8fe9b9aee734ba9b71a8bf63587823993cdeb62abe482ca346b44ddd6c5e074face2404ab3540aac85ee9949b7fcccbb267ecdda9563b01ec32dfb02fdb95d95651aa69afc6980914db9b918dc41f1a7899fb87d103e7151c163da006cbbdbf532172836757b161dbd419f20e0211a484e7f45ecce72af9ae872a7bdb772ca01c8aa03b5ae49c8b9e928de3772201fbac3cb2514d5ca99432247f58a0c5c2584c8f078b226cccd590de3813d3c328e0e22d40fd252ed27165bd755901b974e4a5b6eede05ecb850a1bc001b1014b85ab682f4bb078ef7d3acebc0e23291e2b5c7633eac222bf31dcf22c269374e90de949eb86e6508980a1be81910f4757bb11a978e16033a785f4738609480e7fd245fa98561c56e442f3fa68f101eb2de04bcbcfaa17982cb315e3b44b900b514fd8166024b7db8950d17c2d122d61f75a7cee91aadf6bfc392895044f47da4fd6dfe8a029cece48bfb176d07b9c635aded5ae18ff37f325584ffd18d59c2a6f05ad142df6aed9c54d30192cb6b6e60c300e1e689bd0c9c1908d3c47de6fe8adf8aa5fd4a06cdf45164fc64da84baea30616bdcdf4a8d553cc234bc9fe411d4b7fb0ab5c2f6b53f08d5c43b8d503274b3b84e42d669078bb99295cb6beac6385a0022905d590f5f6356f11131c2b104c36fd4588508d81d030bceafac5f7af3e33515d15f3dc8f4fca40f49b71efb1ba3cb4b6222c232f5a05a269c427aff4b84d443a03de2c454046c2bf2fb672ce151fd6440355d7b0a7f14d5f3539bc705614770b3f10a4ceec60fb3814a5deb35d63bc109fcc556652f9807b49ed688d11d0978d7ac91c06e619e04746aacfb8a6e8ef579f0d30a73a18cbe6968f1b66d5d4d7f9d2291be4325236282ba0e356c458c768870896f70dcb134260344c60c1b56757f56c0d2d1bcff9b9b9ac50b0ed2b0b6efd1643e48382346d0700ba52fdc798934f3abb9e8a373f9532edb977a8a2e62fd7bd9a3678d8e585f443d7a73e52948cdc4cbc5fd65e02f7a7f1847d34e8500e33ed921994a801b87d4eedea5340a03e8cfe562e10f49eb45e84cfc32b7ef4743bd4eb79a30c41c23befbd6b9d27d640a1cf9539ccd8632e636ff88c333510785741722c1ae953938d9c8e8bb7e6ef02fd5c66163563662ed32d8deb51b47de08eef8a82d3ce976228f1d4f79ec0a3ad05288a4f88159dfca23b2011aa79bef7bd0dfff7a491c736418154f903a2082ea27c9b9c230b353bfde52a68a92404f3d661db7e1de9fc802d8d863769cf4b4a4e8ea8c9a54d54f593c52e1f519b737823eb2b76a9ddc21f3c673c15977f5de14d30c9fa4a99dbd0a3b76d1ad7bc32cb176557bf8647d334ead1d2cc1f6cfc212c4333b357ffca8936110c7136ab395af26fddde30f36211abf1cadad91d776c558bcbea6d79251e12969a393f499daeff1fb71ed5f60c11e0b9c1d3dc090030475ad5fb7245b8c758fa6c0158628f0e934c80d107042fb0f41c2017e86976efa5ffec9a50522cffea67bfcd9c69d64f642c6cea494bfddec0ec5aed26486da7cd5bce262437e30b091d38014ad8955532b5bd1612d67b96baf05a4f041f92e249c06e3e78befcb4837fab3c978c8ba072d691b45cbc75cd425ebedeefd328d19f84b5696098f2fde226f29b6e30f35846243e2d93ce9ad59631d5f5d586410856c725565c971967e698e62be353d9a4d20a91522c8490ee805fe544a6bf51ea36a5d5f658c09525c9cd91fb754a0e0fb42113557a813cb6d98bedadbd388a5843ff978a4aca02a209e09628add8782523b9314539d8b879a58f1e4ab523724abb1cfa16a7b97719767e280776a57e18d08f84ffb97f7dece50b679347e98b7b7c68527095b8b989c87980526de6dedb24a8e07baeb94f5bd6f14a432a52536fdfd7357f9118ec1c2151bf35d0d9d8a304a9a614eafa2770185aa1b58fed64448148572b3a9914865b314241d03551f589a070399dc489ba600ffb3efc5eade57657bd8ee9036163b200846022d6d96656278bc64e626bdd1a2396802397bb7fdfdb864c2ab205ffe95c88c39d7506a5f3ae34e306c3a6fdf0c03e03ef398138324b60891af250be51347c1ce05308de29612b9b103ae88827b6ccb49163a1b535747b27407e67d8abcc27998892dda9f53e94eac4468442ec5882f7670ac4a169e2cd58a1f6085d1df1d5a1455ca15bb4e44a9abecfed2d62866e64f1da233912288d758d2cb86c65ab180d27aa63197c620329d95d91942646ac2b35ee70ba228a6b4700631942fdd2db636c1835d1300b1d5e39277346a60a61a4fdef9c7fd82f836735ec6edcf3f923664150da6564f62552596722729ce043371092f5f4027906839b2ec6f72591900a93d2a7322f8b91c92b496abfd289a074029db857c74b9d10d340e1d3e564fdae63b4eef6879a927a706932df958b610b438a2821a4e128ace22812066d02e8772733666d99a9ba21487ca643273bcaebcdc256233bbb9d6d221c9397115d10ae4a549b12751d1603799d579965b1f8db7243ab4f2b4f3c6678bfbac3a90ad20adcb286f4c358607bcc7070df08a22a67110283cc0ad9007fe248b270bc00421e91ce7b3e279fa7e7fc1f3f68882eaf9c84d719604dc65540f15ced4981317b107c29ea9d31de4e914a01248b79db6336f28b27d9dc712d4ff729e154b52f42ac5a6ce9429141ca72d095c86153a4dde84dab4da38a8d58257b728ed58cb3efa234f6b61801fa58c40d0be6dc9f1677d05e3dc97578d7f2e910c597ea5aff2dea13fc9690c0c9dc1e872cfb74ec5ad2595d6e7a546aa8a4d64d422a896e172a85de6dd1baef4d36b0cd489159f92fc7cf2c78a5a7dcb9681107904a8d9e6c5a417808caae6a250bd0cc93c878bd3da8df9d0f6cceb9ca2a8178b276e72282eb3b5c74fa099eff74f170097ca47131602bb559fc7c9b0abc400779dc4be40108cbf87a784a6e8504ce39e3de8b645fb9a93a4236e4e2869c2ca2f12c06edcc9c0bb2160f8a51b68b17273b004ed2c73da345217a1971a09dd65100891477c2038e767fb97327ef4cee9c003b19bd19ec679b04958c9686c09cfcdab532581c9f9a2376fb08acb5fdba0871739c43a146772043d5d8f8c8825931319c8462b8543c1ee7db1bfce7eacc737079f292e13605c5ec7b9ceb166ec4fa3896a50489f0c18af40e8169b278f5da987a97df3b1f6a88a6d404ca06eaed57a0f9d9f332296a0767842227d1feaa5788d6054c051c90210a5ddfd7eba4eef7254f0f52ce81f29d6b19da27454ad5abd73578424758cc5cec1be190894682aaba14089b7f3c8f30a97eb2a65e9ac37ba91d7afe5a7710b8277fc2bb6bf75669c000000ff00000000cca89bf2c9baa2a808e4a003b9c605e74882739a403918cd00000005000000002bd10682d444b401214555948a8a8ad08b24a9778b60d99f0000004b00000000808ec48683f7e4780b34a8098319943ee15817358b0eaa430000009900000000f9da7d2756d48e9bf6ef8afd304ff7853d5e3c64aebebd9000000098000000003564803414f8700f7af9dcdf4b91e0f2245f06ddcdc401550000001000000000c6a1ec39db9b70ab375a2169a3112ddcaefccc69e867e07f0000006400000000eabd6ab208ecc0a94f602b4229fb4bd3ed4b935fdd593c1f000000f100000000678631b8481ae3732fe35f7fdf3b674635bd66776a26e4c4000000a7000000001aee250ac707206e75141ce89d2b05208e3f234ef2c8ae31000000dd00000000c54653cc636cfffcf88baf7fa783004ee3b36c063b8c56fa000000e9000000007b2d7c3b02862ece0831a33e82c2e8bc029ec343c8343c2600000064000000001ff75eb73092cd1fe72821c86fde5501391f5f3821bf8ba1000000ac00000000f416233ad5fc69ba47cab4e14c2bf046496cbcdc8135223d0000007c00000000fb2647b6befe3dc12aadffedb6f7c79ef5d7190e76e54f510000006f00000000f2b910ec90650bc375f330c43dcdd53b6f41c8a9a3249cfd0000002300000000b4bf9acdb6060a5f45162ca135c1a361bf8d051bb228693c0000000300000000a45ced446e3a0e4aa3b525a4e3489e0f65657ee98ba8e4b80000001d00000000b945f5135f07c070b5bba8248c36786da1087bfeeb77641600000011000000009840a25c02072adad087773b807e3bf955133c1f877be832000000fa00000000d7073d59ca587568b7e3cec9020dcea2797a9828a422f6e40000006f000000000badf30a204eea62c63abbb38dbc7d3a438e0905373257fa0000003e00000000952f97f54e46277d57fbdb900808448a5083fa1cb7f05b9a0000003700000000dfc7a052e5c28ee66dd1f89825cd4c025a48635d1ff925390000006400000000c5ba7a964c87f69d77726747b376855fc66dc42dd3efc839000000c500000000e8178c6a3aa47b942972be6ca48fe1a4ba54833f5f63737e000000ca00000000e2a41a51eeef5fd6c5fab17e298e44b8cc7c349fd7ba77c1000000c80000000085fa3d6eebd7833c180419fa33036cd83d50645c2b1a767e000000d800000000fcf99ec4f86bfaa43ec99bdbf45903ccc4832283029231ae0000003b000000009e850e924bdd98805ddc63131dd1270a5bf69a359d655822000000440000000062518e1c7c6fe48a397925b3bb62a47c3f98e0e8b430235c0000005100000000587fd82d147a7b8a1b4c75592242be9fc5bfe15389b7d5d1000000f7000000001d1d011f2b011f2c011f2d011f2e011f2f011f30011f31011f32011f33011f34011f35011f36011f37011f38011f39011f3a011f3b011f09011f1001201501221504285801311201321101330b01340a013e37043e38044235044236044a2e014a2f014a30014a31014b2e014b2f014b30014b3101563a03573502573602573702573802573a095f3a02603533603633603733603833603a09683a01693505693605693705693805693a09723505723605723705723805723a09763501763601763701763801763a08763b03492e7800492f780049307800493178001d18000000e00000000000000000000000001d1c06ffff200000000000000000000000011e18000000dfff20000000000000000000001e1c06ffff2000e0000000000000000000014c2f000000000000000000000001680000034d5606ffffffffffffffffffffff00000001005c01015b01025a01035901045801054001063f01073e01083d01093c010a10010b09010c3b010d3a010e39010f3801103701113601123501133401143301153201163101173001182f01192e011a2d011b2c011c2b011d1901202b01202c01202d01202e01202f01203001203101203201203301203401203501203601203701203801203a01203b012009012010012235042236042237042238043227013426013e57043f57014e1501770908771008005c5c01015b5b01025a5a01035959010458580105404001063f3f01073e3e01083d3d01093c3c010a1010010b0909010c3b3b010d3a3a010e3939010f3838011037370111363601123535011334340114333301153232011631310117303001182f2f01192e2e011a2d2d011b2c2c011c2b2b0121351b0121361b0121371b0121381b01215915012115170122351a0122361a0122371a0122381a0122151601233f0901233f10012340090123401001243f10012440100224521004253f09012540090225520904265808012609140126101401275807012709130127101301293e10012a3e10012b4210012c4209012d4110012e4109012f2909012f2910012f3c09012f3c10012f0309012f031001302809013028100130020901300210013227100134260901353a4401353a4801353a4c01353a5001353b4401353b4701353b4a01353b5101363a4201363a4601363a4a01363a4e01363b4201363b4901363b4c01363b4f013739140138391301393714013a3553013a3653013a3853013a3914013b3552013b3652013b3743013b3852013b3913013c3540013c3640013c4057013d2935013d2936013d2957013d353e013d3517013d363e013d3603013d373e013d3717013d383e013d3817013e2835013e2836013e2857013e3516013e3602013e3716013e3816013f384301403544014036440140374401403844014129370141353c014135170141363c014136170141373c01413753014137080141383c0141385301413808014228370142351601423616014237520142370701423852014238070143321401443213014532060146320501473208014832070149292b0149292d01492b3d01492b0301492b0801492c3d01492c0801492c1401492d3d01492d1701492e3d01492e5301492f3d01492f530149303d014930530149313d014931530149343d0149343e01493403014934080149340f014a282b014a282d014a2b02014a2b07014a2c07014a2c13014a2d16014a2e52014a2f52014a3052014a3152014a3402014a3407014a340e014c2e02014c2e07014c2f02014c3013014c3113014d0207014e1515014f3a5101503a5001513a4f01513b5101523a4e01523b5001532a3a01533b4f0154283a0154351a0154361a0154371a0154381a01543a4101543b4e0155354001553640015537400155384001553b410156354801563648015637480156384801572a3b01583a4d01593a4c015a3a4b015a3b4d015b3a4a015b3b4c015c2a3a015c3b4b015d283a015d3a41015d3b4a015e3543015e3643015e3743015e3843015e3a53015e3b41015e3b55015f2a35105f2a36105f2a37105f2a38105f353d045f3541085f3542025f3545015f363d045f3641085f3642025f3645015f373d045f3741085f3742025f3745015f383d045f3841085f3842025f3845015f3b5301602a3b01613a4901623a4801633a4701633b4901643a4601643b4801652a3a01653b470166283a01663a4101663b460167293b016735450167364501673745016738450168354401683644016837440168384401692a3b016a3a45016b3a44016c3a43016c3b45016d3a42016d3b44016e2a3a016e3b43016f283a016f3a41016f3b420170283b0170354201703642017037420170384201703a5201703b540171350301713603017137030171380301713b5201722a3b01733a41017314580174354101743641017437410174384101743b41017413580175293b017535520175355301753652017536530175375201753753017538520175385301753a540175415801761558227709420177104201353a450100353a490100353a4d0100353a510100353b450100353b480100353b4b0100353b4e0100363a430100363a470100363a4b0100363a4f0100363b430100363b460100363b4d0100363b500100223559000100002236590001000022375900010000223859000100004c2e03000100004c2e08000100004c2f03000100004c3014000100004c3114000100004d0208000100004d0307000100007542580001000077093e0001000077103e000100001e181806ffffffffe4000000000000000000011e181c000000000038000000000000000000001e1c1c06ffffffffe4000000000000000000014c2e4006fffffffffffffffffffffe1ffffffd4c2f4006fffffffffffffffffffffe1ffffffd4d303e06ffffffffffffff87ffffff000000014d303f06ffffffffffffff0ffffffe000000014d304006fffffffffffffe1ffffffc000000014d304206ffffffffffffffffff87ffffff00014d313e06ffffffffffffff87ffffff000000014d313f06ffffffffffffff0ffffffe000000014d314006fffffffffffffe1ffffffc000000014d314206ffffffffffffffffff87ffffff00014d310e000000000000000000000001000000004d310f000000000000000000010000000000004d030800000000000000000000000100000000553a5300070000000000000000000000000000553a0306f90000000000000000000000000001553b5500070000000000000000000000000000553b0806f90000000000000000000000000001563b5300070000000000000000000000000000563b0306f90000000000000000000000000001673a5200070000000000000000000000000000673a0206f90000000000000000000000000001673b5400070000000000000000000000000000673b0706f90000000000000000000000000001683b5200070000000000000000000000000000683b0206f90000000000000000000000000001743a5400070000000000000000000000000000743a0706f900000000000000000000000000011f2b15011f2c15011f2d15011f2e15011f2f15011f3015011f3115011f3215011f3315011f3415011f3515011f3615011f3715011f3815011f3915011f3a15011f3b15011f0915011f101501213559012135170121365901213617012137590121371701213859012138170121151b012235160122361601223716012238160122151a012410110125090a01265814012608090126081001275813012707090127071001283e09012b1012012c090b012d1011012e090a012f090b012f10120130090a0130101101311012013210110133090b0134090a01353a1401353b1401363a1301363b13013a3514013a3614013a3814013a3953013b3513013b3613013b3713013b3813013b3952013d351b013d361b013d371b013d381b013e3548013e3648013e3748013e38480140293701403508014036080140370801403808014135530141365301413703014138030142355201423652014237020142380201492b1401492c0301492d1401492e1401492f14014930140149311401493414014a2b13014a2c02014a2d13014a2e13014a2f13014a3013014a3113014a3413014b2e3c014b2f3c014b303c014b313c014c2e13014c2f07014c2f13014c3056014c315601225915000100002f3d09000100002f3d1000010000303c0900010000303c10000100003d353f000100003d363f000100003d373f000100003d383f000100003e353e000100003e363e000100003e373e000100003e383e0001000041353d0001000041363d0001000041373d0001000041383d0001000042353c0001000042363c0001000042373c0001000042383c00010000492b3c00010000492c3c00010000492d3c00010000492e3c00010000492f3c0001000049303c0001000049313c0001000049343c0001000049343f000100004a2b3d000100004a2c3d000100004a2d3d000100004a2e3d000100004a2f3d000100004a303d000100004a313d000100004a343d000100004a343e000100004c2e3e780000014c2e3ff00000024c2e14000100004c2f3e780000014c2f3ff00000024c2f08000100004c2f14000100004d3041780000014d314178000001");
        assembly ("memory-safe") {
            return(add(code, 32), mload(code))
        }
    }
}
