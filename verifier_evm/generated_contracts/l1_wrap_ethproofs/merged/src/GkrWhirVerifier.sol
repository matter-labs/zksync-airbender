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
    uint256 constant __TEMPLATE_PREIMAGE_MEMORY_CAP_OFFSET     = 32 * 12 + 12 + 4 * 2 + 8 * 8 * 4;
    uint256 constant __TEMPLATE_PREIMAGE_CAP_BYTES             = 8 * 8 * 4;
    uint256 constant __TEMPLATE_GKR_INIT_PREIMAGE_BYTES    = 32 * 12 + 12 + 4 * 2 + 8 * 8 * 4 + 8 * 8 * 4; // registers ‖ final PC ‖ top bits ‖ setup cap ‖ memory cap
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
    uint256 constant __TEMPLATE_WHIR_CAP            = 1 << 3; // base-oracle merkle cap size
    uint256 constant __TEMPLATE_WHIR_BATCH_POW_BITS = 25; // batched_proximity_check_pow_bits
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
    uint256 constant __TEMPLATE_WHIR_BASE_DOMAIN_ROOT     = 0x05F2F0518F231C5E26AA251C6E25027E;
    uint256 constant __TEMPLATE_WHIR_BASE_DOMAIN_ROOT_INV = 0x005C8FF301FEDA030A59F57AB3FE7F50;
    uint256 constant __TEMPLATE_WHIR_NUM_ROUNDS   = 5;
    uint256 constant __TEMPLATE_WHIR_RFIN         = 25 - (1 + 5 + 5 + 5 + 5);  // final-poly log2 = message_log2 - sum(folds)
    // Merkle cap: each commitment is a cap of 2^CAP_LOG2 hashes, so a Merkle path is CAP_LOG2
    // levels shorter. Caps shrink paths but grow every commitment to CAP*32 bytes.
    uint256 constant __TEMPLATE_WHIR_CAP_LOG2 = 3;
    // Merkle leaf/node hash: keccak256 truncated to the digest bytes (the high bytes kept).
    uint256 constant __TEMPLATE_DIGEST_MASK = 0xffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000;
    uint256 constant __TEMPLATE_DIGEST_BYTES = 25; // Merkle digest bytes in the compressed calldata
    // Appended setup data: STOP ‖ setup frontier ‖ pinned setup cap image ‖ GKR term table.
    // It ends at codesize(); all setup offsets are relative to its leading STOP.
    uint256 constant __TEMPLATE_SETUP_DATA_BYTES = 16410;
    uint256 constant __TEMPLATE_DATA_FRONTIER_OFFSET = 1;
    uint256 constant __TEMPLATE_DATA_CAP_BYTES = 256;
    uint256 constant __TEMPLATE_DATA_QTABLE_BYTES = 3353;
    uint256 constant __TEMPLATE_DATA_CAP_OFFSET = 12801;
    uint256 constant __TEMPLATE_DATA_QTABLE_OFFSET = 13057;
    // Setup frontier: the setup tree's 2^LEVEL nodes at that level (DIGEST_BYTES each, physical
    // order) after the STOP byte; setup paths stop SKIP = LEVEL − CAP_LOG2 levels early.
    uint256 constant __TEMPLATE_FRONTIER_LEVEL = 9;
    uint256 constant __TEMPLATE_FRONTIER_SKIP = 6;

    // ── Memory map (generated: contiguous regions above the GKR heap, each sized from the
    //    schedule — see WhirGenConfig::memory_regions for every region's size formula) ────────
    uint256 constant __TEMPLATE_WHIR_SEED_PTR     = 29088;  // seed + in-place absorb scratch
    uint256 constant __TEMPLATE_WHIR_Z_PTR        = 29376;  // z: the evaluation-point coords
    uint256 constant __TEMPLATE_WHIR_POW_PTR      = 30176;  // (scalar, running eq, coefficient) x numpow
    uint256 constant __TEMPLATE_WHIR_ACC_PREF_PTR = 40640;
    uint256 constant __TEMPLATE_WHIR_GAMMA_PTR    = 40672;  // one gamma power per batched base column
    uint256 constant __TEMPLATE_WHIR_FOLD_CH_PTR  = 41120;  // max_fold challenges
    uint256 constant __TEMPLATE_WHIR_HPO_PTR      = 41280;  // 2^(fold_0 - 1) high-power offsets (round 0)
    uint256 constant __TEMPLATE_WHIR_FBUF_PTR     = 41312;  // 2^max_fold folding buffer
    uint256 constant __TEMPLATE_WHIR_LEAF_PTR     = 42336;  // leaf hashing scratch
    uint256 constant __TEMPLATE_WHIR_REG_CD       = 42848;  // calldata cursor
    uint256 constant __TEMPLATE_WHIR_REG_CLAIM    = 42880;
    uint256 constant __TEMPLATE_WHIR_REG_NUMPOW   = 42912;
    uint256 constant __TEMPLATE_WHIR_REG_ZIOFF    = 42944;
    uint256 constant __TEMPLATE_WHIR_REG_CC       = 42976;
    uint256 constant __TEMPLATE_WHIR_REG_CURDELIN = 43008;
    // cap regions (CAP*32 bytes each)
    uint256 constant __TEMPLATE_WHIR_BCAP0_PTR    = 43040;  // memory+witness base-oracle cap
    uint256 constant __TEMPLATE_WHIR_QCAP_PTR     = 43296;  // current query cap (rounds >= 1)
    uint256 constant __TEMPLATE_WHIR_NCAP_PTR     = 43552;  // just-read intermediate cap
    // Per-round query drawing (matches prover `draw_query_bits`/`BitSource`):
    //   QIDX_BUF holds the drawn query indices (max_q words);
    //   DRAW_BUF holds the little-endian u32 words squeezed from the seed (one per slot).
    uint256 constant __TEMPLATE_WHIR_QIDX_BUF_PTR = 43808;
    uint256 constant __TEMPLATE_WHIR_DRAW_BUF_PTR = 45152;
    // do_final scratch: the plain-text tail is 2^RFIN monomials (MONO), then the tail absorb +
    // halving-fold scratch (FEVAL, 2^RFIN words).
    uint256 constant __TEMPLATE_WHIR_MONO_PTR     = 46432;
    uint256 constant __TEMPLATE_WHIR_FEVAL_PTR    = 46944;

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
                mstore(add(IMAGE_PTR(), __TEMPLATE_PREIMAGE_FINAL_PC_OFFSET), shl(224, 0x542d0400)) // pinned final PC
                mstore(add(IMAGE_PTR(), __TEMPLATE_PREIMAGE_TIMESTAMP_LOW_OFFSET), limb19_le(lo))
                mstore(add(IMAGE_PTR(), __TEMPLATE_PREIMAGE_TIMESTAMP_HIGH_OFFSET), limb19_le(hi))
            }
            // Timestamp pad mask 0x3 selects the final 2 unused low bits.
            if and(byte(0, calldataload(284)), 0x3) { revert(0, 0) }
            // pinned inits/teardowns top bits (the setup cap below overwrites the rest of the word)
            mstore(add(IMAGE_PTR(), __TEMPLATE_PREIMAGE_TOP_BITS_OFFSET), 0x0000000001000000000000000000000000000000000000000000000000000000)
            // pinned setup cap
            codecopy(add(IMAGE_PTR(), __TEMPLATE_PREIMAGE_SETUP_CAP_OFFSET), add(mload(SETUP_CODE_OFFSET_PTR), __TEMPLATE_DATA_CAP_OFFSET), __TEMPLATE_DATA_CAP_BYTES)
            // memory cap at calldata byte 285: 8 digests of 25 bytes, as preimage LE words and as the WHIR
            // half's BE base-oracle cap
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                let d := cd_digest(add(285, mul(25, i)))
                mstore(add(IMAGE_PTR(), add(__TEMPLATE_PREIMAGE_MEMORY_CAP_OFFSET, mul(32, i))), bswap32x8(d))
                mstore(add(__TEMPLATE_WHIR_BCAP0_PTR, mul(32, i)), d)
            }
            // Wire preimage: 485 bytes = register u32s + packed timestamps + wire cap.
            // Decode 40 output-evaluation lanes, then layers with k=2..22 sumcheck rounds.
            // Each dimension-reduction boundary has 20 lanes (two per output polynomial).
            let cd := 485
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
            // Include the trailing 8-byte nonce: calldata ends at 21371, image at 12548.
            if iszero(and(eq(add(cd, 8), 21371), eq(add(image, 8), 12548))) { revert(0, 0) }
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
        // WhirGenConfig::derive obtains canonical GEN/GEN_INV via Proth120::to_u128;
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
            case 0 { root := 0x05F2F0518F231C5E26AA251C6E25027E }
            case 1 { root := 0x0185A11C7443AE4CE2A05717A9358BB1 }
            case 2 { root := 0x05AAEFB98DA2664FD6254856A869AD67 }
            case 3 { root := 0x06510476F9662713D6B5172425CBA5B0 }
            default { root := 0x004EFF05AF24B8E32B60B15E311A76B7 }
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

        // 16 monomial coefficients, one 32-byte word each; highest coefficient at byte 480.
        // Process blocks of 8 words (256 bytes), offsets 224/192/160/128/96/64/32/0;
        // stop at byte 224, then finish the 7 remaining low coefficients.
        function horner_16(x) -> ev {
            let ptr := add(__TEMPLATE_WHIR_MONO_PTR, 480)
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
                let base_root := powmod(0x004EFF05AF24B8E32B60B15E311A76B7, qidx)
                cp := read_leaf(cp, vp, depth, __TEMPLATE_WHIR_QCAP_PTR, qidx, cb)
                // final round queries an intermediate oracle: its coefficient leaves fold
                // with the plain monomial tensor
                let folded := fold_multilinear(fold)
                let qp := exp_pow2(base_root, fold)
                sink2(horner_16(qp), folded)
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
                let ev := mulmod(horner_16(mload(b)), weight, P)
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
            // Round 0: fold 1 variables at 20 PoW bits; 42 queries at 27 PoW bits, OOD PoW 10; 28-bit indices, 2 values per leaf, 4 coset bits.
            case 0 { fold := 1 q := 42 pow_bits := 27 fold_pow_bits := 20 ood_pow_bits := 10 qib := 28 vp := 2 cb := 4 }
            // Round 1: fold 5 variables at 24 PoW bits; 27 queries at 26 PoW bits, OOD PoW 7; 25-bit indices, 32 values per leaf, 6 coset bits.
            case 1 { fold := 5 q := 27 pow_bits := 26 fold_pow_bits := 24 ood_pow_bits := 7 qib := 25 vp := 32 cb := 6 }
            // Round 2: fold 5 variables at 24 PoW bits; 20 queries at 25 PoW bits, OOD PoW 4; 22-bit indices, 32 values per leaf, 8 coset bits.
            case 2 { fold := 5 q := 20 pow_bits := 25 fold_pow_bits := 24 ood_pow_bits := 4 qib := 22 vp := 32 cb := 8 }
            // Round 3: fold 5 variables at 24 PoW bits; 16 queries at 24 PoW bits, OOD PoW 1; 19-bit indices, 32 values per leaf, 10 coset bits.
            case 3 { fold := 5 q := 16 pow_bits := 24 fold_pow_bits := 24 ood_pow_bits := 1 qib := 19 vp := 32 cb := 10 }
            // Round 4: fold 5 variables at 24 PoW bits; 13 queries at 25 PoW bits, OOD PoW 0; 16-bit indices, 32 values per leaf, 12 coset bits.
            default { fold := 5 q := 13 pow_bits := 25 fold_pow_bits := 24 ood_pow_bits := 0 qib := 16 vp := 32 cb := 12 }

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
        whir_verify(21371)

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
//    16512 ..  29088  IMAGE (32 * 393 = 12576 B)
//    29088 ..  29376  WHIR_SEED_PTR (32 + 256 = 288 B)
//    29376 ..  30176  WHIR_Z_PTR (25 * 32 = 800 B)
//    30176 ..  40640  WHIR_POW_PTR (109 * 96 = 10464 B)
//    40640 ..  40672  WHIR_ACC_PREF_PTR (32 = 32 B)
//    40672 ..  41120  WHIR_GAMMA_PTR (14 * 32 = 448 B)
//    41120 ..  41280  WHIR_FOLD_CH_PTR (5 * 32 = 160 B)
//    41280 ..  41312  WHIR_HPO_PTR ((1 << 0) * 32 = 32 B)
//    41312 ..  42336  WHIR_FBUF_PTR ((1 << 5) * 32 = 1024 B)
//    42336 ..  42848  WHIR_LEAF_PTR (16 * 32 = 512 B)
//    42848 ..  42880  WHIR_REG_CD (32 = 32 B)
//    42880 ..  42912  WHIR_REG_CLAIM (32 = 32 B)
//    42912 ..  42944  WHIR_REG_NUMPOW (32 = 32 B)
//    42944 ..  42976  WHIR_REG_ZIOFF (32 = 32 B)
//    42976 ..  43008  WHIR_REG_CC (32 = 32 B)
//    43008 ..  43040  WHIR_REG_CURDELIN (32 = 32 B)
//    43040 ..  43296  WHIR_BCAP0_PTR ((1 << 3) * 32 = 256 B)
//    43296 ..  43552  WHIR_QCAP_PTR ((1 << 3) * 32 = 256 B)
//    43552 ..  43808  WHIR_NCAP_PTR ((1 << 3) * 32 = 256 B)
//    43808 ..  45152  WHIR_QIDX_BUF_PTR (42 * 32 = 1344 B)
//    45152 ..  46432  WHIR_DRAW_BUF_PTR (40 * 32 = 1280 B)
//    46432 ..  46944  WHIR_MONO_PTR ((1 << 4) * 32 = 512 B)
//    46944 ..  47456  WHIR_FEVAL_PTR ((1 << 4) * 32 = 512 B)
//   heap end: 47456

contract GkrWhirVerifier is GkrWhirVerifierCode {
    constructor() {
        // Runtime layout: Solidity code (including metadata) | setup data.
        bytes memory code = bytes.concat(type(GkrWhirVerifierCode).runtimeCode, hex"00580f03ab81a51d992073bf084671a21fcb298180095004f3a2961026fa52c841d2137a5da26f0865ad1d165e6d951731260d6fa69f9e569ad5599a663d80542efaf41ed60f753ee790d3454f56568b7a44ecb745e07cfff218b86eb80332b96bdc5c81a0981cfef61c6a3343812df21b4eb782dae745ec6805ea4c171f7e953b15887850b28735a289982e295c2d6076b0b987fd7e85b2f425173c8531cd24d7c370e0b018d1d6627fb99171e378f35dfb7d33596eedbca9a929e8f1e1acc263453be683a1a3528c9a91b10c5fd2d12e68bd97b2b6cd669d005b19c742fefa862ce4fca54533a7a9675f5aaadb80577876f168e6a8ffd52618e960ff1149513fc9366c528cc7d90900261b4b181a68b87df8b9eacc14b2d4d86fe0d84bb65472ca25c63437a7971f913df07842d1a08c7317b02399f676e4b4e5b057f515ec62ede0c48708696f8d1703ecb1df70622cebe9046089934dc62fc63d7b6bb6ce5db88dd4b3105b5094fa893111d89044969f085657dff5f43c438c1251796e22508cd38e1256b023957b8092c077c67cfe7658eed2fa7ce975651a47004bae1b0ba7e8e4c64ddd1aaf2b4ef335d6f06d292b32aecfffba4796b2569924fed4cd39cfe16a702887394813fcabf03b4d9a7404e20fe08a188bff64b00686aa0266efcbf906b7dda051a95f538456a69f3212213b59eff0d49c67a87bf0500d0d79cde807e35b80f62aac70bc02b7c6a73ffb6d2e33099e50ec91b5fb03e61e28041bc75b6e3c6ace69f8b63cd415660dc829dfc3b253590d6b4ef2d63f309972c5b6d76775d65caada3fb55c1de623f708c6b4986eef7e46d47233e40d7ee15dcbcb943ca5c0b9cb8f00ef35315cb9888f15734c00753e5c173be487555416fecde52e17814824bcfef60b48745476cb7d6d549d479ae7307c54395de14f726e818a8ef9136e96c880a648166523a83a2737b0f5c7d0bcc1ac3b4786340526061ea38245f6b70dfa985c0384a167a26d79ad4e2f0b75d8febafa49610743bdd793abb19f863c957efcea01f1eeae9f03ad4dbcf05189003323a41598e9235fcedbe017cd1b1df472cf4cacc3432cff503695a83da7ebb7f5e4357506478aec9424a0c380916b16a99cefcfc8e52f1d13b72f469518986a49d2a1ba7699461cd40f214520cd6313975bbef85eb513f6651fab28bace482f0880071b2745176ab7cf2a4fb5b5aea880509aa9e917c65dd9723b64738d9e0e46dc837325d809df36813857bdb95ecf123492913906a583e5c822b83533518588d4223b3902e469701953617d588885919b8d8e9a0063be465c6009c70fd9c43d03365b50521b972b27bc22784bbd0f2efbe6daa8b0dcb30ea3d07bc8c0fe806c14564fc5658a8cf0b7ce1b53399a9a8902830c83a146edbfae6f7dc56b712263d073257cac33b5b26f2c334c3237da453e138089b6a7e6891423f790e3c6f86c64ce2ce980f163d0aac4cfa405a31e413795e2b7e4570379190ae20f76eeda2d04ebea03f22c90ef2989403df1748c5a1442630aaee471a73c970ff6896e7291c169ba7b95734634310caab94a189a44be0d633a3c27728ade506b2288da7f420f8083fddcb1f94d5627aac2aaf722562f64681dc8112e915f025c3189bf79be7f80df1bf3686524c64b6407e1408711fca0b4fee100be44dedb55c0948aba6f140acc3023231e0954a06f63f3979d6ba1b548587f160006a5ff84901a66968e41ea9ea9389e0aef0b765e8a1435ac4a3cbcea5408f70e285a69df06a2ffec5416a1aaa05cc353bd174395c89d8779f48fb7deb7b82be3832ff77518ae705a49a11df9f88d76233de10ef2bb1e1d7ef4ccd478ced26e662579d78e57ec5416f0aaf78eb998a1a1b5d5317ef16ae5c7fc6d2ff3fc01b757ae3f1c2e665824456aff2e6ba678c12fced3651bb03e6e21d6c0ca2fd36b85880bbd6033e65e8ca1aaee298b46f986c3c5d7b277fa9bcf36b696e07c1120c87c6ee1113cd5443fb6303ffeae3404c4ea5882f58be8adc35a26496871d573498d067f5af2ba50f1c5985c42b312887f97da52b866beac0d5079542298fcae290b64b4be2710f1573ce453126823ecbaf9d49006f7c12b23bf109df0bb03e45f748a89114c9bf97d46556f4f68b7800f1c9d0e8ffe5b32cf81bff10814f286d41d3e874e99bc03e45721dd1e8590a35e9d47d4e5b9cfca2f4f1c67ee8c85c606aadaadfe8ead3640f8180d764dbd329624bcb31103856c6bda8a04e684afbc7574bdd383be274079d463bc075dbd74b9e14d37bbf3c221983736d29c3477f78833ab4d9fec597790fc8ec4ae89a13f522714ddf2b89ed7d8fa5317abbe6f70d7325da5aecf4f2996b5289f3022e441ee365c1be279ab09ff05cfc2ac048a58e5ea533e03dd57050c4eb28d81dfb343b5331f903cfd26029b204085c85bd8f01d8c255b37a27ccdca618bd7fd2e8af48299440dbb2dcaf0e251d983a16c45afee4a8188549b1622f869aeaa7b8584202c29f3df6eb4346b089bdfbaf726127475eaa43b5e9e9721133b255852829721be3d4934010b314750193b7cedc321ad482adc78429c7fa0b9f28881e0519cfad16cb435d0bf8f24e2aa347874860ef1c66e5e4c8322002c66b75300c92359cfe1285d074f6429371ec3a0557a409cdaf4b326d830e1c2fa524b84ec818fc5876db2b72bc393610ce9ec3bfe7075621401c0c8c2b1d735130e0a2c1bc79d92b4395625fe482e7e5e6b53d2e310630434dbe8e7d7fa3818bcbfe7a249aa9d6aee38f91cf687ccd95d233ab5eb8ceacc23debdd71daac6eb5d5f9f9edb69a12498e4ce2cb1c91d50fe0bcdc136633d7f415859af28106f9b206cff5882a53c7576ee5c98217e47d9a60b35367afb3f266e57245815fd17fd6e26a0eeee75d0b9a91bb1db011b21f4dd52748554849cb73948647d108725a6e8b9ba8fbe1e278aee3477fec60cacf1ec8bde2c10c0ec919db87d6523bac6963faa53659699fc119efc2c4df8b3c3c5d7c7288ab2bd5866ac4e5acd613b15e79bf26fc1cd30d79ae9f43e10088c3b4797d1f228fdbbf8e7b3a7ba6a1337b504cd0bf52ec43bd2f66ba19b1aff0b7196ab50566796555e0a72d47536abf12aa781e605fd28e5542c5af206e89f790e61d98d77713f4ff6eec9a3d4bf885dc86ef9348225db7f210ff58ffef4d64513ca8d0a185f52982b91862d613d1bd779c727357087e0cbe250e91a074d6105d3fd351e90cb541c6f78f63bc0bf76f1a82bf5f864a76415eed34e843cc4d328cd13125164d10993208947e8052200d6d712577cf90dec0d0e7210fa39964688ec5bd6ddcba415d4190f26ee4074f3845223ea01d2cc4344a1985c0d286d059f2cd59ef9b417877220a8bfdf324892d05980231da0c779d84b1c02d37eeed39597e108322c4caa8a22e167de375ff906daf2fdf60dde27766fcb186149d1cfaa26acd2c52ae8cc5833e7c7c9cf080f02873b6088ad82973ad21d2a4da9fe3507241d83beb2302b7d656225b04b09e7e51b23cf78ae8944a84f61d6572bb17ca0c47ec8b26f2dc2e25d6020b995a2ef1f298b66b76aa1ad544ff8fe9720d763de6f989c7d7dbf772ead10217553cba3618861b551f5d7582d6432f95d4f0aed13d47f79e549377f8abf7e321d0bea1dfc51e7fa5924cce44378370706987309aef2b9730101e8f0b697bc7c616f455225c39b95bb1579c5a638b23f0bf7b3caa6c91582c336e7281a5166acecf461d3cf1bd758f8c39086c15ac6ccdddb43e299f64a5a579e4d2929578c9018341d5c0ecbcb46b920ab0e0c12b46e8cffe876891c84c0705b97e09db20e4208644170e47c9bd607700e1de8b1ef15c305ee42d75fb31bb761e870c289037f8fbbd1c386b6e3bffec3f43e6f4846b8f8af82448549fe385eee3ce7c2776f6fc2ffd657a04e1ea501c36f9cec122791783cf0d8dd82c2b2870a85fdcaf60a8c486394fd7523aaf58a289f4aa4cfd060e13b7f5d714237d7727af8d42d1961d7b2d9abeb24c86004859064b6407a27bca2ef646671cf17485034d77dedd32b5dbe4b4e841095c9b8feec3b40c39176b0dd94c918dbbd1468ebd452c8a740c29f090ce7fe7db449152bc767545f99f2caec039235be26b7d00255abbd9441345c1e0018d87b322743e97f388da73ada38f65f9f75de710c5ede865a9f0591c5f5fea04566d4ff32e71e1d7c4a02fcd1a550e8a97e149c1af941cdb6c4082662786ea92ecd6da9011bf96b9acf585530ef305740aabb1c0624dc517698169c0e0fe3efee93748578664c23e466f165956522224d121449d12ec181bfa243da4845c5a0b5a1065b898f3aa530973de6b0c416288a4cc29855549af4358b912601c0ba56406997e4228c4754f5d86e7bc71b031d6ad39dac5b4b2705a9ad3c0b518a478c6e8a44420cbc4075a0539a56bb8d04f2b5b792c8ba31f2416f7674cefe2325b76f04fd7754950f79df2592db96384e5301f5e0318474c88092028d354bb69af81de7f089f227a388424dd42b041d5a007c69cdcdfe8fdbb8baa74d1ef88b93a3fc8f87171425f169a131de7de1749973ea3029e5e4c5f061446c892395ed626fe4f696b1d7700ee01d0188ec3afd4820160e60022da0387fa43ca69be69295dacec63214c2ac59a3e8b042dd8ca534f0bc43d404bc7be6096f8fb49ae9362375374151530d121ab9d7b856b8988979b070105bed5abeff6188f7ac5192c38a0fc28f91305afe316c9b10d6d8495ee73f8e509ce3c5d2555a17c804f0ea69d8a8ce3ad522b3b45cfd97de13ab8f6ecc798017278a9cd3d63b214181ca8cf00b20d753983a701744e549759c480c6dc28302fa7cbbbd0a939fb4e175ea65e16f2ccb93ca6f1c5665628ff92f1c3c4b7c39411dd389ce40250ad83350f28c63603245128df42496674f9eb7264a17ed2a057db4ba5f561247ea694bd8db1cff5fc496a4f39b0ecbd1254dc0fae9b6348ada45780a52ee2b9b15a683a2297c4fbd1e6563ea72d51bfff47b77ffd8af1d3a3297857ef0ba8e15646aa15a9e80b563945b8ea3566c2a4c23bef95076588a84f1b0cfc700fe16036593ea66058406f8fd4bd2c9fb1a3de33c411172e3e5e114b1fa5496f29157d689c566acfc8c8ce93f98d4e915803d38553bea2a65b396733b41e6b175a1b6b1a5b6548bf068d0da6a6e748328774bc8c8d4fd2be3b9dbaafa652710b84f1aaf999d78fed7e98700bc14220a8071361299630c9500b9c797b53b5523de96453f1c232bd56651530e1a16d7e286c5106c19efae854f8a6cf9ec6228d67a51377fd1e8e70445c753bfb45423dd8328c55efb96a84e874a4b9050b2ed9602030bb7b990e89691ba351e24e61a1ee954eb34626d9568ef99d620b3017d1e5c18eba5529d2c3ea36fc7e3f12ce7c7ef7acb6aa5ef2ab639f59bc809d38354ea7dfc1faaeab3b05782fc7fce77c86bd9bc273cb46949fbc139ed3741d3d1d7c41bad6a0fbd21dd7058f727570584e8b4b6eb64a456472c013e28de7860d44472be6aed4973b1cf82e0e80abca59f9d7dba5c6311ca9f16beb8affe717dc9ca2b9c6d372946ba60bab9e788b6566763a4c386d7d6b02a2a6c1c20fd0e610724ff180ba4d10515f48f1fd7529425683ab607bccf496c3719de47e6a7c9e1e81e5d4e7582f42d390cfc91a126944e9dee2fe6c3fb9cf4d1a02e9cf1ed0fdbc7a57d853de5c00bfdd41a45b3e61ebd51eadac23b06873e1d9628c0c9673061204acba3e426a18b69146b713bdb4388aea3994d0691d37e40651ac1020299c2ac2243b341c8e703ae999e0708446819e22b0b797c970cd032f492c90fb17a00e6e401cf7e45c3e4cb74484a1749749e9262326d317730537a7549d3c134d14eab534887ffdf2cc24bc3f54ceacca4c4360089b3f7e98541596b4b9757511a8f66f18a8f8986387537aad789341479205db081047d3a954137ca48073a4783dba0ab0477373cf6fa57c21044bfcdfe205500d527b0ba1058b9c4f73a448676edf2c45b9dbcc6a5b7bfaf700c11c6d35e1c717ed1374ca4d2abcc73441c022f29af94c64c2e8f6c9943bdaf771a27d2c78ad0fe114ddf0e192674acc293290526808891b68ce74e6d187a9a4859653addab4941e813b2777c98cced10223e2d11a54f5edd89a724d576be45fb6a75fc2aa6cbb43fca350bcfc42920688d6d818e92b0ac09192641231bc159c1c57cab25ebaffd8bb3e3ebac3ebdb6dd50f94b3fdbd3694931a939b1c3146fa27dd56cc10f7577dbc509de0980f0e6c2fa7eb19ad1109dff6789d4f17de96726df02ae1ebde610df58cb718c0aeadd8c2ca69b80caf4eb73ea46ce2cfeea8dca4581ef202c19210c6ab42fc770f8e10eeb7efe06947bba6224e373b2d1f85794474ecf13bfb798b0db58a4debe807f3d3c78981e3c8157806c42da9da8beeebfdf93e00eca3e6f12d2e8fe430b968d3e0627600a452e6fb4a7d5775400870cc7ce1a0eb72690cbab13c6137d97fe8de68a2762b49e52c873388773c66aa10c585b9ae7dba8c661da93a647d85268c63545812c1dbf56cf76287cf6b07617269c20e07a3f1215d056f1a2b9a8008cbaa74ca91cb42abf390619deaed6045bac3cc406ea44859b3da68e9752b14f5d1e45ba6b14ff66143941579320886984f3be09afa2a1721c90f774001abdbf86db2d6555d91f0885485f39654ba3d20526e16c74ac45f12ce6461bebcc0f962dc8962267a49d11937a5fcf5b81aa05eacd8eed6b33f47fd7ab4c82ee55e087f33b80ecc1715c7bfd6bac48d0e8a83fa8a047cfe6cf6343f35a96af7ef42bf63afd7946cd2342aa3b71364c798533b0465b706abc31859e89fe388ba0bb3edea84bd3332e65c35419d84f5f11c6cba321c9a73b3cd872d19cea81a2617283a195d71c4780a36ad17bcf1d9f36eeb1f6437a83c10cb2e7d0f37980412a84bd0af5cf404ec6e2c8feed1c5ab89c174e703c494b5067f9eb8649dde29275279e5a2a8eff804739b6ac51d14bab0ddf6afd0f29306ab1c646f03b5a1ecdbd3cd7f830b292c1e6775893f303471ca3b3dfd624751dd1ca5c81b68f8feb43bc45b92661414ba54d4f0351cd321a2c45c3185c5f54f676e8e66b68b45f1291108ab09d3c5086461c4eb457c113a26f02dbaa113252af4475216c31f8176d7d0c9f68a541cc777c26d72e5459d0459abcbfd69a32c75e51e9102af3f8eb6e079d6bb4d170556a24250346e342c436be8d00c7e3a2aeb25585462703251d41ee52bfb79bbf3c9991420ad7b356a7482402155d03967ab794a7a3841c40aabd9206f986b24643de032cd988b1a315002c02ceb73b4072536dde04ecefd418d2f12d2a1e5dd09bbddf0afdbef5de7273bfe063aac14812a24e4966b92732995264defc476b9600ea285632aeac7c62ab04aed17048117ed5a2e63fee3dc70f9c3cd89c734f80b38c22f32f7b98f8aaadf303a7b9fabc464529bb64fc5ea9c384ba5b056bf2e8641b60305d12a9cea5800d2cfc9d748ce17c97cef9cb7f3681dacaf4506956fff649e56dd5ee4c8e52a2ef5d9a4afdb5d301c8668a749c8ad68a8e54179d7d4fb8a07449ade1fb86074ca9bdb0cd1c03771b9e1f69b2c2f74deff38db812775b0c84c6c455a0852df56c2c14f841ff2fd1dabc2a5dd73314285f0650074ddadf9f8b216a15403868f8adef0cc1a6067ec8fccda67db29468c3af0b89b9d24fa4e5ba909c8e751060efe2a828d3e69b06ce644b61feb53167776e70b573dde4f2ff074a4d539ca9f6f125a83c3c5a082539c87d4a58e71df0626fd14482c14dd47dd984a33b31c636ee9874fa8119ae2c43c1694c837c0f89f3f11b9a4f072ad78661dc776c6bafcea6dc42cadaec7940d87101b7b8672d8f6d71ff2194b7a347b895e12690f6c78c67413e57cd335fd0cd93e46786421d87023c6050d5c408c140d77791a5279a1375eb5dfe0763641ad452878b385559da092620dcc5f44d5880f0f0a7613652a8755280c1babba90f37015d20e414c1de07e1a556fd88328a551169903a0de0024781ecd7e7356cafc3114b572743696329994abae34cf7b97d329336791bebfa6671c131e6bc117120fc7eb926017009c6cbcfe4f24f9bfc153af7bd3c80a432e28c2cd30b2ae71ae3ad09686e1f032db84a812c8324f9b8dc242af6bc1df9b7e9352abaad72d12ec87991c5505db629de871092296ba1f1028cf08561002869e599563f2234c0fa04032c2f9700bf2bd7b5c88b6efeaabc61b8c21be5b68455163eb7c04a8f43b5f0d76a4a7a8792874db20acf1cc35dfa99ad89afaa947d7dbb7a740f0e409aae934255665d986a5d7c9635e5de66dd82d08ef811dda37dcc67af7ad916af58191a532d53a7ad40104760ba9f1c2d328352a501bfd211c311642bdace3670bb0791660cbdd1f0c00b634fa831b1eadd43d8e0182c8534876f3ddb86d64698bf5546f774654970641dfc62fc1e7a24a14dcf83810806c5a62febef592a0fa5ea97f58549de1ca5fb3f44c4b167f77e528ba45960f8baf1f29e57e3038e7f60308296490f18fba810bd0ec60265548bb944d92aa2a86a5ac704a69ae3f3fdaca56e9866d78324fa9a912e660cd2cd88d14a06cddd90f86b4dbd2a36a875fdc9c4d2254dd1172dd1e5dc33af782d9f52e58723d17455ff17b8e6e231821dbf48a9a373f6bc8b5e4075b5c58178d3e477950c2d5618e464cedbbfd95ec4734f72bae7cce3c32a029d6c045fbc503c409ecf38acf079debbafc8008a35ea8081697d5c767e9209be04c871de2f71a52a1a8bec8d6f14937fe893b0c879e07cbee8b0cf5141772b85c63652b84bd711dba82ec9e8f158d4d231bb13cdad3068593a2e668e463a46a5346a8e5217a27e323b8ca39907d6f07bbffaeebb4241271357028e35f8141cd0570390aa3a1a3e9b7ccb921593bc498448aada6298a1c6c475d4c91985e77df50712d6926acde9a4ce342e461785f523398e9a465229df803c5c3dc7c12e0531924f7b8d0d0d39419d1ad11f0332fea6c3764fe33cdaf699ff12823e0943a123650c9415b8af7df3ba39b6b36162953468bf0c8c86dea4560c0e5b69db686420d97dfd2ead4c5f74e0f2200edd48fb1c297460eeaef1d30820bc4e87e13287b5c2422f550b9b1ec99e921ceea842de901064808d518fe7f65aac116b4eb79f18eea419dad35d39d83039b5e70475e80263939e7124126bfadab23121d49caadb3e4eea110cc08ca153f05c952fbe72d41975998d0c9baec86ce346bd10e53957e4c2776cf97ce0e91bb1aa877dedbb6c802727b8e80e80bf23eaad723f7455af1115caa64bd3caeb81b9b8a4b778ec26242d20ddee26879269217135a29a27c28f3b654524e3450fc815ba005dd4b3ef75e02c05cec8f7b7e80e5d892bf3b9498b0cc0fcba164cc6f7bff0e96e1441f00fc464d9f31081ab25e46f3c9bada4d53aabf8bf067b15a8d083329dbf10f225f41122458657c46c6bea73828921c4caf5d6e290562b12334777ad67da3805ee48f26972e7630dae702d884c2cb94b5c7e9758cca8a82bea9dc4cf04be7407ce58f7a772b7f072724b00d729cfbd02f0fe08ffc69083a8cc2244a2551c67cd0ab813d8ca319c4df4076b3b841f2f93abd6193efc78fcc86f925d13284089547c6a02a3cdf44a07acae4a019346d0adc19097c789fa55190b52143d33547c9c60bd7a68359d0aa160a9eab448293b694ba374b974ddf87ee6ac75a4e68338a254cca18571107b9feb162286fa958c93000f856c5c7ffdfb90f9b4d9418a6d6bdf92c0061d1d6f81d169492387a53135c96a6560a79e058dba8e531581932493dd5cdae44e8cdb1b923ce2f1579bcf3c0c747cf3401db1526ee481f38625bb1a564a38052cd8216e25f8d0490225448c9c65284c1682fe0488255f41a5182e1f2d0f9958891122d7c8462155fc0b3e76c7dec9a059866594059ba917f4d6794859b3f702d898865a4f0827bec541dda315d9760842b5aca932065641a0ae7143027b83b49522bdd6b9aeabe145c356591a57d03ede3044ca5a718964f09122636ae2b0a498f246747317c9a1420493ce5c188ae567787981a5a696fbc041296f58e0e1917b2503b8fcec73405a7cc9731aa67281525d55015f03c14ff8bf02a7fc74901251d87e12ea6a1bd49ce641110c33e766f1fbd33a6285109e21b99cd79c4b0a3d7ea0c1c1e97a2e3203d613191bb87676effe293cee8a52aa5694b5bb86827b7acf74f6fd780d945ca3cafed4d237c3d99a6f043f7eb79c917f723579832ce1d09a757449fcf2ee1e34484e63c5a6fccb3c05013d832951c7dcfff1a4eb3af4944082fe0e70377eab383a94dfbced9f2e95f2e0cab815ad058d4cab25d95055f0328412fe8e5cadcf44c95f6b32f5e1c245f27f7d962959deff1d9e37e42e38c89fdef6dc36c5a40c9f95f01672b5f5c2e043d5fb71d64bab8a5fe98fedc44ec54eadb848edb2a9aad418058179a24ea13200933c0c5397b9934b62726c66dd0a14ea3733b35483ed9c5ade0b2fbb429b1ce8b18da25d39900e4622202b5fc30ea9fbb9a24e75c25ea08e61a7a44e91ec52bfa77db870f62bb173f715b03ae6a81cc1681aa9a001b60516eeb5c7563638a5c4e4dff7fd492e4e9ec5629823ccb3d6dae5073ac419056710fbae03b25cc5e802f1c3c454532b1599a6161f1c253692c6bd08a7695073d3e5195a97cfc00eaa4a83c286edc9b6b76e6430edec9f156df4996e734e971e8eb97ede7115b0ad875acc9e5197f4a89a5ed8bdc8249dd77ca22ff1d88571c5fee49aa14949c05be62715855c6a6fe833a453a81cd213e1fad9491664e38ac0f1cbab72426c0da8fb78a3df79396f1395b0d1ba55a4e3d1cbb9270177b8306762dfec5dcf0de03411efbb2e18231319a355dcab826090aad301c3196ccf316eafe616b3fde782def117c580605a20d7078345e69dcbfe29c90496f094df8ae45747c3742eee4f22dc0ed8e6d42b0b25881c14b116a7d13ca507162884ce2f548379ab6e639ebdabcb783aa7e2c963077ac7bbedbac6a4740b318b043fc4b9e557d9656961022e261553a511f9fac7e009fd2a4a0220a57c93537b030026417ef3e866ee9694944b6d8b0d8111f5d6550770a58462edee1ac886e03cbec995da010e108becd8328ddb17e02bf6c0e45e444d6114aca76345479a3cfd4f83d7a9918bbcfd809380e23554726da60afeb28e2e476a7160ce2c689af1028d07ee90b7db2426d69e889f804d3e23c9f77b55d45debafb49ee2a285c85ccba890121b087dcfb3a41c032971c0e4c74f7dba2a91d2057a9b8f8509b3b04c835a7a422c16a034a14e929c5def3bfe2aa28aeff53e7f836a93c0224fb1d641204235aeaaa12f1abb59b474f43be7c4ba35b9c2766a29131da4628bb9780cfa531f8749116016e20f052d35a47540b4008775ae7687c7294e33c2a90c3c0370159ee8361eb33d57774e401e609f616353361f7253f4e696653d8261f6e61fde9f9636672eb3b538aac7f449ceb81acb027d1020161faaf55b2a459d296714ff7c6ee7959c21d60a9fdf31df0005de939ee6fb6313e3a6507aeff71344db69f881d3ddfbd0e75b7cfdfabda1cbef9236253e658803c1a355e914d268ac454ac3a71eadf5e22a8c03e605a093fb311b09ad696037c9d56c7f6047ac475ae3abb655250ab38ae221e5168d9eac7dff743f54445a07e123ce1474aa065f3aa6e11f307cf0e7f9cc810b3e6f39e2bc318d0129ee5e054ba4beff2c1ed503d385d4d13ef662a762044b071df53154b83991f7df15850c7b08ef57080d896c2a838a3fc189660a6998dc141bfd1aee42c481ad33d1447f00ef67a3da3d160440a5eea078311e863c352789e11ee9dab8bf4e2a53187a354fc5cf559abec1031360878d41be51e4f510626b59ca1856c17c5a452b5c455f146c99b97364ddfc5c78dbe8be90fafd071504d983610460fbc57087f03ca92b7736efe72bf75102ec9d8bda3ffab4e5545404409893815bfd9bb4f7c4ccc9221695de6eed728e25cefffc3cd50e5d5bd69ed59716f4d353580924c123b8e730dc4bcbb39ef3cd72c5c7fcded5ed622b685549ecd23476f720c6d179f60ba1c63da552cb1240e1c9b236b96449692da2a2c7aee945eb4cb0f867fdc913389f9d93ee5bb8c3a34115997973fd8ac3ccaa7e6f854c17d0acd211d8aa75dce7315c65cf3a873a548d1b4ba04079e4df9106cf9868a9a2904381919e5584f6ab23cce6dae3ac85243cc3cbf53fef24f30469a8976b774b7ef8b2be33d3d95eda6f2333d304b90bc835c021ef62d42cd0e46f6eddf1d75679ee36636d56a3cbaa25f94f5a552d6112553725fb32b64a70e081d56b36e6c47c90dda1a82ce58920e7f68f94b4a057d9363baaac5736e26ac997cb0ff1ed4bfb49f0708cb45640ad506956719e1d1000a24593e7b47b7ed4bd0d74ac528dbf0a4909e6fcc50edfd27ad7ce6d81348c555f570e48db7a1a9a5590bd377cdca2d58ff4ef3a7202466adf687fc43b412cad3ca9cf087a3e54697bd8a14a2d3f921e85f9bfe9a079f5a98014d71c94d72d509d616cb9a94fb737d14606ed8b088d70b192cf079aed22332f1817418a33e70662b83aaf16606386c963c5c9a504c97d8400ebe1a5a96b050c96021b4856636a857e65a2342a466103c313713a53082d21158d25df56627131189e26ebab6d14f0143032111ebfde81a127c651ade94af7c52612a0d72dd405139437c649feadd53723563a223a8183e9b823af2390b061895d7a7ef9e4d1272058f57f1f2249aa5ed3aabfdec345d9adb3bae12356694e59f54e02d9dd4df663715cf8d3927c1369568b64c6b07ab3e23bea823c8343490a25e1daf67ff6cb35097d8c514ef0619f3cc50beb0b059a971c966223a04df3a98842b6ca88402a366f50767564a9b4cd26f97efad5e3dd2358b4091860566059b435247129037a8291e0ee06f44200591817d352706b9927130dec835150dc4dd42dc6f5d12389901311d4cfaaed06b455b877b19857124f55a421649b8c9f934450d3ba3ccb30532d7f4e33d24e1b75bf3ca8a381d5d0d42b74e23239477fe99ba0702a019d8e0f0ebfdbe4120d8996a4e47c91dd407c57b48ab126703b05f6c0193944f37332037b852926d3ed4f00ba3287d0851e851e8155a251cbd76f77df0bda3dbf60f3f0b839a78df87f8bbbe5e12033689b629834861bf08be38a59869c3064939cd2abae4b37ec373dc6c60a39c966e807b13b79daf550ec068bd7b7b73db735326991c5a63529e7f13c8ca87b8f1b03c253acdde2944009af1faac836a5df9a8e50c42184f18077f9ca237fa8157717043d0b247bf4d45afd5ca2967023abc0cca73094005c5311d3796f028789e23dd964f1982a250f7d3eeeac16c95475d9e9204588e3d27f31998cbc0fadee5465139c2d2ae8dd890d3e61df6155532a19aabf8b8b075cd9ad9ff05b795beb1fc2c5b0d2fc7b1d2bb41579158430b5d27b9d09f858df55c3de4474dcf452d1df673bc0623557ac1c21c2749757790e053a58d0b1c39e7a2021d3e3c6fc03656efdc65c5f3f94457d1790a905f1eac9ccfc9e3f21d87f96f0e749de4a675ab1a2129b2df30117a065fff63a7ff6d4f095150de320ce7f441dfe835191b18d3b2db41558b961ab9a98e89173a2c084762c53c237d433923c3804c5b5de73e641e34aacd6d2c15023388a68930ea75500fd77c1ec9c168dae33616aad52590f1241cc91396b6b6205eb9763260790a8cffaf8a462bf267d40cafd269eb9f0dfacf24eed53d826c60b78532864fa8c5535f40d32867cbf3dab27f3ea088ceac5decf35c8fe57dc79807d58042ccf3d666f427db52acf606e4a7dde0b755159e0cde126be581dd7f9a1971c7143eace4393cf5d92282c9469742dd470494e5f94de0cda5fd9bbcb6a59b6954d6db85cd14d335d6b793512d26aeb2afafcc30f259f204e9ad4808ef4baac6f4105f08379babcd2cd3382a85cf0182d17c727ca00e7db861c33275fdd4280dbe1fa979fc191c1ea71fd48220f91b18333f73128b8e05335109ff43f8493209ae56a9a53d9786832cd67f811e56f2d5e992058297e2a085f4417375d7b818365a88802a6dc5e7633113b3d2595765a74d9f342c0f3c77fbb0fd4d09855183b7031ba478ac70f5c8be5367308cf97d5631f6f55bbb5ba1bbafc419cc94de0ab0b2206afd3e8a46e5237cce7582ad3a58ba72fdaa352fc5c29616e28e1aed35f192817f4ed169208bb1db93e6bad2f4d045c56b82314dcb033a9c6c667143fd2f474ab5cab243d59e5ec403dab81829718c24ef9587db54c54bb4dd8d84e84c152d24b6b2a3e8eb6c31c382fc8a5c7c2eb113083c14156f72c614b192cacb156c5dc0d4a78c40d098c50c7d92d0f5ee5022d923a8def546aebbbdba13a66bd55129fea8341b431a3b4e9ac09862890d63c6724c99587ecbd4a6fecbb4931f5f2af220d2cabf725180fbf3f1e3bc915e56023659e132a9342b54be72d41f8db945054b1a42f78c5e9467f4e101396bee5d507fd1bb40aa679123177c0a264ba1158c8f8b51359c6d439eace237eb6b864a6917d546f60daba5e93e82e00c18c551a56ca4253d76a07c6aa99680e8b33ebde731d12b979cad9eada5b378da40f64acd62dcee18f62ae912c4287aada2bf66b4105cb2b79ef36bf5a382db6b653d4ee5517a49d346ffa45a666334d733e678daa6d4f3c86b1a148b95dfc1f0ccc33e877d90954b4cccbce7f38a076298826fb79182d3e4a7d1778a320a897c2b2be71bea9806a780d06273435eca12ecce157861fe3d93010ed4324025a1dbbc2d5c53e276fec9f08ab827e73c039256e220ad1c5f5e4b3e5ea25efdbe7b9afed5644436040ded82bdfd9dadf432479da13974baa49072bae019d8baf49ffd90edb5f5320be3bfae5fa954c8081309c03570d6998bf8defdaa86395698c50ed364e5edfd0ff5b2c0e3df614af5869a8d5cd931820fab79655a125344ed4e496aca215985c753dfc3e53efa24cd2ed69cf9ff95f99ca54b2b13523cb22f97996587ccdbcc71324d414cb7148fc53215b3fca660059b68b09a6919b4ca16e46d279d5261460b5f53138abe9bfd183092922f506c646aeb9a0d0677c83f2dcfad67d8e4be9fe8f3b3877b8133cf0852d408db535b1196108e1afc600c93c5698f1f9f07054ccc5308c2dc563b8d7fe2bd8e60f0223ad9ae4c28c7af1c79c8a1059fb91a4e61fd9eb287b67f79d8c7f740d0ec6bc2b3474eb67349cb5e2d27df0da0bb0598ea608a7df96ef9c7f5899a234657cb144a3a4d7314a14e07a6ecaceaee6511854743d56c617284c727158580a2663d90d026616c1fd677dd95e8e3b706b6959179e0f783f6c7d87181842b37b4f89c71f80c50f98adf769953bc29c1aaa8fe6ddb679955e5f641f5d53a647eebfb010ead92f6c89770c68d57107912a61121b37de41d118892d824f390cba5f46c3e5655758657edaf66ead21afd54bffea110d076c83a5ada24480653473ae3f4b097371f7dde73d34e43fcd943214e42d1dd2587fdb4cbb22d7a67cf5a1cd727add9e99373db7ca1993e998d0e964c15606c9c3ee4d2ba119a6c939d8a1c78c41616a02c2891abc64c00d5d58e17603c951ffeabd429c906ba4e83e873db355dea23ee2b8e9a31f53a58b670d03d0fc49b2709778a92da7194e525ded6d5dd0d5e524dfd710461a796675b74c941b5f793a5c44dec623f5bbe0803a8c85659e2e8939761ab3bcd4c2cb8e9f9e7446febd67508a996daddd5ae9d785d704446d0464ac57981dc3e007df0d8d52a3df3bfc01c31e0080ad945877b7b7796aca4ef471c1859ae3e8c428d6b0f1e6b92254bc7b0110d075858b7db258736add74333301601a39f74a39bd4560d0fce65c14c979196b7c991629e089daae767d3fc280440b9117245ad534336cfc06882eb631e65f91ccd93e78347762ef83536fcac68d61e9fb99db96207a3bb18de8122a4d1cedfeb8d78161ba4ba3fb75f2a195c975739d8591a1142c093e0567169e8b66193a4ee57f4063b2f5b8fddabb1ff52d8145c40b701f09956a31914edc4cbe0424b6a61a85d226567768fb494b69a06d433282b796551ded0ab63a80d4f24f48d4af66228e086c204f9f576993df56a7b7d06612554c5beb39b2fbf2847e34b880c6a9442794f857d703db808463328c808454bfe51ae39a4cb7e1ccaacec138691f800e5a24de30ab31a95b75535f55987a74cddaf9d8b0e6efd91da9d7fa7f273337ac1e05cad5196fc1ed73a13d240cda776aead85a0ac3f51b32f2be77d258677573c7daaabd9709b64c0441d3c3e1023290a33d97affccc5c044852cebc0c5faf111f140be1c574bc294595f7f519e498d592a13167803f887fa81a2593b2616fc3700831234d247af02c014ba6b2184f8d649adf44d61f2b4450bf58681b7f85182e937279c536e9d1de1926d7d11e6dc2f195ee6a4976b197ca260f8591a98e6fa04416503f2a16e43df915a5c190722f9b1d873d79c44f93a3ea34470c39b94f07fb234291518ad567584e60c5f902e003456f3b68f0db7b2da4a1df8679b923e29886fa3b092cfa9b466ea709953e8104f9d47835a2084d1bc582717fc143f37f0485a22c6672634fcdfb414ee6d664819561a11549264d6ef20819c15cb0dbfe44a0c5460c1d25055ceb7057b446280055bf0742a39215857970c81d89680eed045918da53b5605d4bcc6309d9dcdca65be2c7fe1258b8a9dc3e0b6a9819524d5734955eca8571702bcc6c2c686fc842d4cca6d525c504cfdbd5df73e4d19a4ccbde3ada574c7310a6c58c7dead1eaf3e84ba79139e7cc337cac564f0fc92519c4da0bb36d0279e6359fd43a18d0e76ee7757c2bba5222f66ab10610e14dda98adb977a0d707902732816152b5396055b34a4f59c5cd7d86ea9e9b53979fc1391bffcbbc565581606d64c37c7dd7710f078e9cfcc03c1825edcd2900b3ceb2ff0a644f94b7e7ff1ad82289755be5df8dbac2bd9fc92524f65ccae61b9c95d6c416be0ae0b24c0b9657d6182fffec987cf301fca9cae80ac0cc48bf189cee1c8cda9a9ca5722b112a315ad000caf84634328782d881fd56cf201508d6e68f5cfc2e5c58c12bed3c1b48b7f399300192f4a778e2ab8b9ea7922f358fcd4349aa765d7997b0132c68a400f42b32058f0d702d37891d3d4f1480d92b32d933e3030bec8cae6a8db734ecfdca21c501a0d96704f9c7f26ef30afdee5aadf5636acf4a206f30da7be01ff96c27bb81397c9b9afb7d35404808f1fba7d9aa29ede6988ee5b4614c4ec9ae4d2987cf1ceb1753d26573f06a2af5dab196fc157d9747c7c8fc6e44bb31988c4f184a275aea7adb35f97d5831ff6d3c0e760100e6c5634cd3fecfbd016751cb4c8d90ca9431b16f93171091130e261df14f900d34588b9f3d64249bb13a5836066234506f8294b4246f49a72e6b0cf6300d7711a1f82180c37db2a9e3cd4ff52fc4211d4706cc20b579f6de44f13892e72289d2209a1cfb2a2819d0c40996f028faa271f1e7c52b0f01302cc792f419c79124bb42a448270528635e65e065a0223e8f4b96cd1a75405ce3481876f4565c56b44934a3b621056f12255f9ad4005010647b4737ce7903eea0fd0903ba8b871cd0136aed987acb6dd3416ec27e84b5f758e35a65567e14e5d5e66c21c4fc92a577ddb63db027163f4b2c9708c8b29cab902821635c29e0b339704710ed1dea93b4ef1d4642bee52ebd833778fa6cf64f0d58b79eaad40b854bffc3c60d583cef23d9f8691a334f2b587b3d1e9bd40652b9694144568bac5d32fc938dbdfe96a5ce9336f37ca40ef360a7326803231d2cb029b6bc54dee40bed0c0df7e9970808b7d2a28eebe48f503774a03af0c7214650599c82ec5d245e032c50ef456957264a72a97cf0e90af820a60cabdaa942cbd17e9ee9222834b86ddf4080e9c297a4f01e765921bd0db6ff56d4c32ca5b4000000af000000006bfeadeba87f455deded49bdc98b84c4ed8759b83568107f0000006d000000002143c04a26629bb64872d05c5d149dcaaf9e780968c3a2a20000007200000000db870653b8a6953dc405080d9b4d0092f6bf7b2201e8dd82000000070000000064ce1472cc7156daa3fd7818293fc4cfd661c1c073ad2a70000000b3000000000a2092e450b6bac5ff552d9715f83cac8d6ea68ecc2e63950000009d00000000f76356a2ccc8f898e6e4c1c185e7f0f8b029ed8e4a39b834000000b8000000009a6c5334e87bc199ba6d2cdd6c5c3e066d73873a11709863000000d0000000001d1d011f2b011f2c011f2d011f2e011f2f011f30011f31011f32011f33011f34011f35011f36011f37011f38011f39011f3a011f3b011f09011f1001201501221504285801311201321101330b01340a013e37043e38044235044236044a2e014a2f014a30014a31014b2e014b2f014b30014b3101563a03573502573602573702573802573a095f3a02603533603633603733603833603a09683a01693505693605693705693805693a09723505723605723705723805723a09763501763601763701763801763a08763b03492e7800492f780049307800493178001d18000000e00000000000000000000000001d1c06ffff200000000000000000000000011e18000000dfff20000000000000000000001e1c06ffff2000e0000000000000000000014c2f000000000000000000000001680000034d5606ffffffffffffffffffffff00000001005c01015b01025a01035901045801054001063f01073e01083d01093c010a10010b09010c3b010d3a010e39010f3801103701113601123501133401143301153201163101173001182f01192e011a2d011b2c011c2b011d1901202b01202c01202d01202e01202f01203001203101203201203301203401203501203601203701203801203a01203b012009012010012235042236042237042238043227013426013e57043f57014e1501770908771008005c5c01015b5b01025a5a01035959010458580105404001063f3f01073e3e01083d3d01093c3c010a1010010b0909010c3b3b010d3a3a010e3939010f3838011037370111363601123535011334340114333301153232011631310117303001182f2f01192e2e011a2d2d011b2c2c011c2b2b0121351b0121361b0121371b0121381b01215915012115170122351a0122361a0122371a0122381a0122151601233f0901233f10012340090123401001243f10012440100224521004253f09012540090225520904265808012609140126101401275807012709130127101301293e10012a3e10012b4210012c4209012d4110012e4109012f2909012f2910012f3c09012f3c10012f0309012f031001302809013028100130020901300210013227100134260901353a4401353a4801353a4c01353a5001353b4401353b4701353b4a01353b5101363a4201363a4601363a4a01363a4e01363b4201363b4901363b4c01363b4f013739140138391301393714013a3553013a3653013a3853013a3914013b3552013b3652013b3743013b3852013b3913013c3540013c3640013c4057013d2935013d2936013d2957013d353e013d3517013d363e013d3603013d373e013d3717013d383e013d3817013e2835013e2836013e2857013e3516013e3602013e3716013e3816013f384301403544014036440140374401403844014129370141353c014135170141363c014136170141373c01413753014137080141383c0141385301413808014228370142351601423616014237520142370701423852014238070143321401443213014532060146320501473208014832070149292b0149292d01492b3d01492b0301492b0801492c3d01492c0801492c1401492d3d01492d1701492e3d01492e5301492f3d01492f530149303d014930530149313d014931530149343d0149343e01493403014934080149340f014a282b014a282d014a2b02014a2b07014a2c07014a2c13014a2d16014a2e52014a2f52014a3052014a3152014a3402014a3407014a340e014c2e02014c2e07014c2f02014c3013014c3113014d0207014e1515014f3a5101503a5001513a4f01513b5101523a4e01523b5001532a3a01533b4f0154283a0154351a0154361a0154371a0154381a01543a4101543b4e0155354001553640015537400155384001553b410156354801563648015637480156384801572a3b01583a4d01593a4c015a3a4b015a3b4d015b3a4a015b3b4c015c2a3a015c3b4b015d283a015d3a41015d3b4a015e3543015e3643015e3743015e3843015e3a53015e3b41015e3b55015f2a35105f2a36105f2a37105f2a38105f353d045f3541085f3542025f3545015f363d045f3641085f3642025f3645015f373d045f3741085f3742025f3745015f383d045f3841085f3842025f3845015f3b5301602a3b01613a4901623a4801633a4701633b4901643a4601643b4801652a3a01653b470166283a01663a4101663b460167293b016735450167364501673745016738450168354401683644016837440168384401692a3b016a3a45016b3a44016c3a43016c3b45016d3a42016d3b44016e2a3a016e3b43016f283a016f3a41016f3b420170283b0170354201703642017037420170384201703a5201703b540171350301713603017137030171380301713b5201722a3b01733a41017314580174354101743641017437410174384101743b41017413580175293b017535520175355301753652017536530175375201753753017538520175385301753a540175415801761558227709420177104201353a450100353a490100353a4d0100353a510100353b450100353b480100353b4b0100353b4e0100363a430100363a470100363a4b0100363a4f0100363b430100363b460100363b4d0100363b500100223559000100002236590001000022375900010000223859000100004c2e03000100004c2e08000100004c2f03000100004c3014000100004c3114000100004d0208000100004d0307000100007542580001000077093e0001000077103e000100001e181806ffffffffe4000000000000000000011e181c000000000038000000000000000000001e1c1c06ffffffffe4000000000000000000014c2e4006fffffffffffffffffffffe1ffffffd4c2f4006fffffffffffffffffffffe1ffffffd4d303e06ffffffffffffff87ffffff000000014d303f06ffffffffffffff0ffffffe000000014d304006fffffffffffffe1ffffffc000000014d304206ffffffffffffffffff87ffffff00014d313e06ffffffffffffff87ffffff000000014d313f06ffffffffffffff0ffffffe000000014d314006fffffffffffffe1ffffffc000000014d314206ffffffffffffffffff87ffffff00014d310e000000000000000000000001000000004d310f000000000000000000010000000000004d030800000000000000000000000100000000553a5300070000000000000000000000000000553a0306f90000000000000000000000000001553b5500070000000000000000000000000000553b0806f90000000000000000000000000001563b5300070000000000000000000000000000563b0306f90000000000000000000000000001673a5200070000000000000000000000000000673a0206f90000000000000000000000000001673b5400070000000000000000000000000000673b0706f90000000000000000000000000001683b5200070000000000000000000000000000683b0206f90000000000000000000000000001743a5400070000000000000000000000000000743a0706f900000000000000000000000000011f2b15011f2c15011f2d15011f2e15011f2f15011f3015011f3115011f3215011f3315011f3415011f3515011f3615011f3715011f3815011f3915011f3a15011f3b15011f0915011f101501213559012135170121365901213617012137590121371701213859012138170121151b012235160122361601223716012238160122151a012410110125090a01265814012608090126081001275813012707090127071001283e09012b1012012c090b012d1011012e090a012f090b012f10120130090a0130101101311012013210110133090b0134090a01353a1401353b1401363a1301363b13013a3514013a3614013a3814013a3953013b3513013b3613013b3713013b3813013b3952013d351b013d361b013d371b013d381b013e3548013e3648013e3748013e38480140293701403508014036080140370801403808014135530141365301413703014138030142355201423652014237020142380201492b1401492c0301492d1401492e1401492f14014930140149311401493414014a2b13014a2c02014a2d13014a2e13014a2f13014a3013014a3113014a3413014b2e3c014b2f3c014b303c014b313c014c2e13014c2f07014c2f13014c3056014c315601225915000100002f3d09000100002f3d1000010000303c0900010000303c10000100003d353f000100003d363f000100003d373f000100003d383f000100003e353e000100003e363e000100003e373e000100003e383e0001000041353d0001000041363d0001000041373d0001000041383d0001000042353c0001000042363c0001000042373c0001000042383c00010000492b3c00010000492c3c00010000492d3c00010000492e3c00010000492f3c0001000049303c0001000049313c0001000049343c0001000049343f000100004a2b3d000100004a2c3d000100004a2d3d000100004a2e3d000100004a2f3d000100004a303d000100004a313d000100004a343d000100004a343e000100004c2e3e780000014c2e3ff00000024c2e14000100004c2f3e780000014c2f3ff00000024c2f08000100004c2f14000100004d3041780000014d314178000001");
        assembly ("memory-safe") {
            return(add(code, 32), mload(code))
        }
    }
}
