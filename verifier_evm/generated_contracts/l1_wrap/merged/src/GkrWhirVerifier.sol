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
    uint256 constant __TEMPLATE_GKR_POINT_BYTES          = 32 * 21;
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
    uint256 constant __TEMPLATE_GKR_DIM_REDUCE_LAYERS  = 21 - 2; // trace_log2 - OUTPUT_LOG2
    uint256 constant __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS = 21; // trace_log2

    // ── GKR→WHIR handoff (generated; shared with the WHIR half where the names coincide) ──────
    uint256 constant __TEMPLATE_WHIR_CAP            = 1 << 3; // base-oracle merkle cap size
    uint256 constant __TEMPLATE_WHIR_BATCH_POW_BITS = 14; // batched_proximity_check_pow_bits
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
    uint256 constant __TEMPLATE_WHIR_BASE_Z_COORDS  = 21; // layer-0 folding point length (= trace_log2)
    // The WHIR half's own constants (schedule + memory map) are spliced in here:
    uint256 constant W_HALF = 0x3800000000000000000000000000001;  // 2^-1 = (P+1)/2

    // ── Generated from the prover config + circuit (`__TEMPLATE_WHIR_*`) ─────────────────────
    // Every value below is assigned by the generator (see the note on `__TEMPLATE_*` constants in
    // the GKR template).
    // RS-codeword evaluation-domain generator and its inverse — a primitive 2^base_domain_log2-th
    // root of unity (`Proth120::TWO_ADICITY_GENERATORS[base_domain_log2]`).
    uint256 constant __TEMPLATE_WHIR_BASE_DOMAIN_ROOT     = 0x048B6B79BA191BD30B0910E6758FBC8E;
    uint256 constant __TEMPLATE_WHIR_BASE_DOMAIN_ROOT_INV = 0x0521CD7F2760EB0D44309DC8A890B5C2;
    uint256 constant __TEMPLATE_WHIR_NUM_ROUNDS   = 5;
    uint256 constant __TEMPLATE_WHIR_RFIN         = 24 - (1 + 4 + 4 + 4 + 5);  // final-poly log2 = message_log2 - sum(folds)
    // Merkle cap: each commitment is a cap of 2^CAP_LOG2 hashes, so a Merkle path is CAP_LOG2
    // levels shorter. Caps shrink paths but grow every commitment to CAP*32 bytes.
    uint256 constant __TEMPLATE_WHIR_CAP_LOG2 = 3;
    // Merkle leaf/node hash: keccak256 truncated to the digest bytes (the high bytes kept).
    uint256 constant __TEMPLATE_DIGEST_MASK = 0xffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000;
    uint256 constant __TEMPLATE_DIGEST_BYTES = 25; // Merkle digest bytes in the compressed calldata
    // Appended setup data: STOP ‖ setup frontier ‖ pinned setup cap image ‖ GKR term table.
    // It ends at codesize(); all setup offsets are relative to its leading STOP.
    uint256 constant __TEMPLATE_SETUP_DATA_BYTES = 29210;
    uint256 constant __TEMPLATE_DATA_FRONTIER_OFFSET = 1;
    uint256 constant __TEMPLATE_DATA_CAP_BYTES = 256;
    uint256 constant __TEMPLATE_DATA_QTABLE_BYTES = 3353;
    uint256 constant __TEMPLATE_DATA_CAP_OFFSET = 25601;
    uint256 constant __TEMPLATE_DATA_QTABLE_OFFSET = 25857;
    // Setup frontier: the setup tree's 2^LEVEL nodes at that level (DIGEST_BYTES each, physical
    // order) after the STOP byte; setup paths stop SKIP = LEVEL − CAP_LOG2 levels early.
    uint256 constant __TEMPLATE_FRONTIER_LEVEL = 10;
    uint256 constant __TEMPLATE_FRONTIER_SKIP = 7;

    // ── Memory map (generated: contiguous regions above the GKR heap, each sized from the
    //    schedule — see WhirGenConfig::memory_regions for every region's size formula) ────────
    uint256 constant __TEMPLATE_WHIR_SEED_PTR     = 28704;  // seed + in-place absorb scratch
    uint256 constant __TEMPLATE_WHIR_Z_PTR        = 28992;  // z: the evaluation-point coords
    uint256 constant __TEMPLATE_WHIR_POW_PTR      = 29760;  // (scalar, running eq, coefficient) x numpow
    uint256 constant __TEMPLATE_WHIR_ACC_PREF_PTR = 33312;
    uint256 constant __TEMPLATE_WHIR_GAMMA_PTR    = 33344;  // one gamma power per batched base column
    uint256 constant __TEMPLATE_WHIR_FOLD_CH_PTR  = 33792;  // max_fold challenges
    uint256 constant __TEMPLATE_WHIR_HPO_PTR      = 33952;  // 2^(fold_0 - 1) high-power offsets (round 0)
    uint256 constant __TEMPLATE_WHIR_FBUF_PTR     = 33984;  // 2^max_fold folding buffer
    uint256 constant __TEMPLATE_WHIR_LEAF_PTR     = 35008;  // leaf hashing scratch
    uint256 constant __TEMPLATE_WHIR_REG_CD       = 35520;  // calldata cursor
    uint256 constant __TEMPLATE_WHIR_REG_CLAIM    = 35552;
    uint256 constant __TEMPLATE_WHIR_REG_NUMPOW   = 35584;
    uint256 constant __TEMPLATE_WHIR_REG_ZIOFF    = 35616;
    uint256 constant __TEMPLATE_WHIR_REG_CC       = 35648;
    uint256 constant __TEMPLATE_WHIR_REG_CURDELIN = 35680;
    // cap regions (CAP*32 bytes each)
    uint256 constant __TEMPLATE_WHIR_BCAP0_PTR    = 35712;  // memory+witness base-oracle cap
    uint256 constant __TEMPLATE_WHIR_QCAP_PTR     = 35968;  // current query cap (rounds >= 1)
    uint256 constant __TEMPLATE_WHIR_NCAP_PTR     = 36224;  // just-read intermediate cap
    // Per-round query drawing (matches prover `draw_query_bits`/`BitSource`):
    //   QIDX_BUF holds the drawn query indices (max_q words);
    //   DRAW_BUF holds the little-endian u32 words squeezed from the seed (one per slot).
    uint256 constant __TEMPLATE_WHIR_QIDX_BUF_PTR = 36480;
    uint256 constant __TEMPLATE_WHIR_DRAW_BUF_PTR = 36832;
    // do_final scratch: the plain-text tail is 2^RFIN monomials (MONO), then the tail absorb +
    // halving-fold scratch (FEVAL, 2^RFIN words).
    uint256 constant __TEMPLATE_WHIR_MONO_PTR     = 37344;
    uint256 constant __TEMPLATE_WHIR_FEVAL_PTR    = 39392;

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
                mstore(add(IMAGE_PTR(), __TEMPLATE_PREIMAGE_FINAL_PC_OFFSET), shl(224, 0xdcfd0300)) // pinned final PC
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
            // Decode 40 output-evaluation lanes, then layers with k=2..21 sumcheck rounds.
            // Each dimension-reduction boundary has 20 lanes (two per output polynomial).
            let cd := 485
            let image := __TEMPLATE_GKR_INIT_PREIMAGE_BYTES
            calldatacopy(add(IMAGE_PTR(), image), cd, 8) // external PoW nonce
            cd, image := decode_next_run(add(cd, 8), add(image, 8), 40)
            for { let k := 2 } lt(k, 21) { k := add(k, 1) } {
                cd, image := record_factored_run(cd, image, k)
                cd, image := decode_next_run(cd, image, 20)
            }
            // 5 circuit layers, top first; each at-point count is a 16-bit descriptor.
            // widths_word stores layer l in bits 16*l..16*l+16; 0xffff selects that count.
            for { let l := 0 } lt(l, 5) { l := add(l, 1) } {
                cd, image := record_factored_run(cd, image, 21)
                cd, image := decode_next_run(cd, image, and(shr(mul(16, l), 0x006a004a001a0012000c), 0xffff))
            }
            calldatacopy(add(IMAGE_PTR(), image), cd, 8) // WHIR batching PoW nonce
            // Include the trailing 8-byte nonce: calldata ends at 20262, image at 12196.
            if iszero(and(eq(add(cd, 8), 20262), eq(add(image, 8), 12196))) { revert(0, 0) }
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
        // register final state and PC in the transcript preimage. Challenge/addr-space/index
        // constants:
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
    {  // InitsAndTeardownsHigh: Σ_{k<7} 2^k·r[14 + k] = Cache(19)
        let gate := gkr_virtual_poly_compose_vars(7, 14)
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

    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[0]<<7)) + α³[32] + α⁴[33] + α⁵[30] + α⁶[31]) * (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[1]<<7)) + α³[36] + α⁴[37] + α⁵[34] + α⁶[35]) = 6
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR(), mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))), mload(P_PTR)))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(7, __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_0)), mload(P_PTR)), gkr_memrel_compress_high(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 32)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 33)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 30)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 31)))))))
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(7, __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_1)), mload(P_PTR)), gkr_memrel_compress_high(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 36)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 37)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 34)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 35)))))))
        let gate := mulmod(lhs, rhs, mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[0]<<7)) + 0) * (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[1]<<7)) + 0) = 5
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR(), mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))), mload(P_PTR)))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(7, __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_0)), mload(P_PTR)), 0))
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(7, __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_1)), mload(P_PTR)), 0))
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
            case 2 { root := 0x0293B319B108C8A856BF8B8AB7799ECD }
            case 3 { root := 0x048B6B79BA191BD30B0910E6758FBC8E }
            default { root := 0x048B6B79BA191BD30B0910E6758FBC8E }
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

        // 64 monomial coefficients, one 32-byte word each; highest coefficient at byte 2016.
        // Process blocks of 8 words (256 bytes), offsets 224/192/160/128/96/64/32/0;
        // stop at byte 224, then finish the 7 remaining low coefficients.
        function horner_64(x) -> ev {
            let ptr := add(__TEMPLATE_WHIR_MONO_PTR, 2016)
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
                let base_root := powmod(0x048B6B79BA191BD30B0910E6758FBC8E, qidx)
                cp := read_leaf(cp, vp, depth, __TEMPLATE_WHIR_QCAP_PTR, qidx, cb)
                // final round queries an intermediate oracle: its coefficient leaves fold
                // with the plain monomial tensor
                let folded := fold_multilinear(fold)
                let qp := exp_pow2(base_root, fold)
                sink2(horner_64(qp), folded)
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
                let ev := mulmod(horner_64(mload(b)), weight, P)
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
            // Round 0: fold 1 variables at 10 PoW bits; 11 queries at 27 PoW bits, OOD PoW 18; 31-bit indices, 2 values per leaf, 8 coset bits.
            case 0 { fold := 1 q := 11 pow_bits := 27 fold_pow_bits := 10 ood_pow_bits := 18 qib := 31 vp := 2 cb := 8 }
            // Round 1: fold 4 variables at 10 PoW bits; 10 queries at 25 PoW bits, OOD PoW 20; 28-bit indices, 16 values per leaf, 9 coset bits.
            case 1 { fold := 4 q := 10 pow_bits := 25 fold_pow_bits := 10 ood_pow_bits := 20 qib := 28 vp := 16 cb := 9 }
            // Round 2: fold 4 variables at 9 PoW bits; 7 queries at 30 PoW bits, OOD PoW 26; 27-bit indices, 16 values per leaf, 12 coset bits.
            case 2 { fold := 4 q := 7 pow_bits := 30 fold_pow_bits := 9 ood_pow_bits := 26 qib := 27 vp := 16 cb := 12 }
            // Round 3: fold 4 variables at 10 PoW bits; 5 queries at 30 PoW bits, OOD PoW 30; 28-bit indices, 16 values per leaf, 17 coset bits.
            case 3 { fold := 4 q := 5 pow_bits := 30 fold_pow_bits := 10 ood_pow_bits := 30 qib := 28 vp := 16 cb := 17 }
            // Round 4: fold 5 variables at 10 PoW bits; 4 queries at 30 PoW bits, OOD PoW 0; 27-bit indices, 32 values per leaf, 21 coset bits.
            default { fold := 5 q := 4 pow_bits := 30 fold_pow_bits := 10 ood_pow_bits := 0 qib := 27 vp := 32 cb := 21 }

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
        whir_verify(20262)

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
//     2432 ..   3104  POINT (32 * 21 = 672 B)
//     3104 ..   4192  SEED (32 * 34 = 1088 B)
//     4192 ..   4224  BATCHING (32 = 32 B)
//     4224 ..   4544  CLAIMS (32 * 10 = 320 B)
//     4544 ..   4864  EQ (32 * 10 = 320 B)
//     4864 ..   6912  ABS (32 * 64 = 2048 B)
//     6912 ..   9280  CIRCUIT_CLAIMS (32 * 74 = 2368 B)
//     9280 ..  13120  GATEVAL (32 * 120 = 3840 B)
//    13120 ..  16480  QTABLE (32 * 105 = 3360 B)
//    16480 ..  28704  IMAGE (32 * 382 = 12224 B)
//    28704 ..  28992  WHIR_SEED_PTR (32 + 256 = 288 B)
//    28992 ..  29760  WHIR_Z_PTR (24 * 32 = 768 B)
//    29760 ..  33312  WHIR_POW_PTR (37 * 96 = 3552 B)
//    33312 ..  33344  WHIR_ACC_PREF_PTR (32 = 32 B)
//    33344 ..  33792  WHIR_GAMMA_PTR (14 * 32 = 448 B)
//    33792 ..  33952  WHIR_FOLD_CH_PTR (5 * 32 = 160 B)
//    33952 ..  33984  WHIR_HPO_PTR ((1 << 0) * 32 = 32 B)
//    33984 ..  35008  WHIR_FBUF_PTR ((1 << 5) * 32 = 1024 B)
//    35008 ..  35520  WHIR_LEAF_PTR (16 * 32 = 512 B)
//    35520 ..  35552  WHIR_REG_CD (32 = 32 B)
//    35552 ..  35584  WHIR_REG_CLAIM (32 = 32 B)
//    35584 ..  35616  WHIR_REG_NUMPOW (32 = 32 B)
//    35616 ..  35648  WHIR_REG_ZIOFF (32 = 32 B)
//    35648 ..  35680  WHIR_REG_CC (32 = 32 B)
//    35680 ..  35712  WHIR_REG_CURDELIN (32 = 32 B)
//    35712 ..  35968  WHIR_BCAP0_PTR ((1 << 3) * 32 = 256 B)
//    35968 ..  36224  WHIR_QCAP_PTR ((1 << 3) * 32 = 256 B)
//    36224 ..  36480  WHIR_NCAP_PTR ((1 << 3) * 32 = 256 B)
//    36480 ..  36832  WHIR_QIDX_BUF_PTR (11 * 32 = 352 B)
//    36832 ..  37344  WHIR_DRAW_BUF_PTR (16 * 32 = 512 B)
//    37344 ..  39392  WHIR_MONO_PTR ((1 << 6) * 32 = 2048 B)
//    39392 ..  41440  WHIR_FEVAL_PTR ((1 << 6) * 32 = 2048 B)
//   heap end: 41440

contract GkrWhirVerifier is GkrWhirVerifierCode {
    constructor() {
        // Runtime layout: Solidity code (including metadata) | setup data.
        bytes memory code = bytes.concat(type(GkrWhirVerifierCode).runtimeCode, hex"0071ae757f6c923802d1e0b1dac65a239e937b10e0e5ef4ec8e14b65a1481e3bf33a747c945279d39140a3f0bc593916cdd1fb9d1644e4d5eb0ac11a48a335188eb11f59f4190fd499564dfbe68927ef434e5990f9d83493b95b1f07234c1084fe94164aa6cc0ebdbc28b7d91ab0a97f50d17f2da2946d10706a1feb0a8ff3c7ba2874bfa7ac7d9e2fd224abd5688a943a7a6e8d59f3d106c33da7a705ad58f4adba706f29c23272ffa0225b038974867197a914cd221361124395d3a14452fd3118c6c772ec0ac1dfcc5e8c7c5ce062b9961b944bdb84800f50484e81c3c526c6cf466cf0efb1b4ae2a4ee59e3aa595685538ff06847d10bebfc21a51a58e97a5859789f6f95ce6e923914e17de9d067d645fc76247ef22c3d9c4ada87fd044550b63036cef1b5c9e7bd105489b403b0aa937b4f753440cf2127f17c289cb6af9a63185919e10192b94975801bdb500c95ad759f5ff755839401152f9cbf5d4420e624479440be026d58a5f1c9d44086d27a4e8e522e4e3189cd4efa81848bf22c937135408b0c4d1f06369f076ac6b3071f53ae9c9879edfb72266de7fc1729e91e5101252929d490a521b6f81c54e3edda6ce4b97ff4ac3d1d5a0093b60f225fc05b928007404462f7448282a1a7e2d2b95518686cb5754719c017224567e170a883939e7929353f3114e652a631ab5145d2ed881995cab4365e2607bc6a928675c592434222c70bb38b6039883a3761360bc478b8124026f0bbf7070e28f4a4b178596f7c0ada50214b09c11b622de806554bbe6294d495e4e734a2d0835c02ae021f372ea02d5f9bb6e09fe2534ec29e3a672766afb1f42b7bd1d2d60169f28e00cac55bcaa0041ef5dad756e4ba6a308b3d1732bba7b502e0ef61d8874d145ba42fd87cf7822909d4c478041a022d561b5ea9ae736d353fbb3b2c05bea07a90847e22c59374a6aa84586689ba14f4366c1c17ebfbc03bd4ab1cb7177dbd1e1f4c74c2cb317277d6a81b8b410e770780c3e0501f4dcddba9cef8634e3ebcd790c6e7000f6a92145e1c482eb03eaf9cf1b1fbeac10d169d79994ba87e152e466ba91fdd9a4310a3d58027d253e050c19b2aa42f3026deee0c02f5f8dc5c3289482288c4d5ceb73ebc412cf95f1c13127c3bd65bf540f4d176fe7069121b529e8d7535865ea4da4f00479e436b358e0430fa2768a4d3eae9254ee43fdcf21e577ad1cf08a8f1a6f61cda972129a4c80a182a28210919c5b96d38354020543edcec3d3df4f7377914be33601bec6d04c3c2cc53b201674511b7855a56b1bcf2f12871c53a999e0e6d3b2b5d79b2bfdc6a079befbcddb327f079ae7653794bd51cc9e656e31f8fe167eea0332cc83d1282384ff2c1de54eeeebc38ffa616a9db3266cf0b71c3c4d6e85a65e71b6bbda0b43117cab86766b6e56a9f0060ea0390d5d60cb2919e59fd7e3722a00879ccbbcb3cd2d53c91c61152de7dc1dc725d861f00817084d7aaac44e9bc4acd20b4aee9a34587e6e215b235b2a3a0433c0971220bd00d410b3eef023911a1c02b93bbdf6d7cde1aee261bba003a3d040e802dc806c1bcf623bc5e32badb98e7b23eed08a987b9c3a0c8840644f08f0d90a7a772e1ec535f869d079d5d941fddc993f1d384a005b6675e3a97f174f2081739c1ddc937833e222bf1b54f55aaed2c9838da915ecd9df42cd10b0e3e15ac6494d19a61db732d3a6374f0749d85df31ec45b0bc0ecd69e200617ce284c37617cba510158d6263ca58b04b793b847da8d6fa0e8d64202203d32f77ff5b2fff668015ff2a733ac36ae5309fe8d5e0f68c466eff663cedeeb0eb81d1e5646f0d2dec0a9c93df1c0b573e4e02c55a07e13b7258f4fddf176c224353756a6a8c8c5ca7b670040eaf20604baf4f4229c472b7c0a7c714a8900e1fe864d196244022b465347b1ae8b57b8c709987260f166e29970fbb770d14c97394ba72621996cf35db1eadab80a8ff222ec465e60fbe04b3dadbfb8a64548817977b3571a3dedbf62d829584f8ae4a8a813bc1eb1800bd71ee6bdeeb0462ae9682cd91c9456a8e38ae2f8df09789a96b425ea900910da0b4e532c70771a139409df775025f5c7ac0734dc79f53c036fa457c08eebf90c621ba843eff7cb28a0b940519be144f1df7e0e73e64d0369c81a662341c193a052fe05e2e3bbc8cb5b50daca7dbc30050f3a7e94bc8c81d19e2172ea00dbc10efb677995213c1d2995974d0dfadaa7aac98aaf0cebc8fb9e8c5f7698fb3f474417e00eaeafa62b944437049d3c8c50dc3027f22fcf3c7f66915c5292ce79a4350495d0dfce71476c3dfc5eb21a6fed56c6a5567b421f8f7433cdefce3fd5c28a0a9d162432fda6c0b3b84c072bee0f73684d281533230a0d180f6bf74c30a854a0f10751f72aa86404131683efea5114549751c8790fd791666b3284e58c46b44fd56ac705d81c71773b7db7ca9cfb120f05975d4a9a2bda1cb0f714d50606cc063464d0d643a7f095a190abe4ed5ab03ef094c378449b5f4a750008f60eed8b25136d7c81c016715b75a9f9481896bf8a1d984e955b3387dd9efb371e9f8ec7aa3a5688e5bb120515e02499f7371cf0928c1b706e818d6bf784d895ac08a16aaa83dfd40b3dd4766829d098f6782a5635193a86927ece92115f7f84a52113cd4fd84c989581372727761a9551cc1b09cf97a147d156b7995c2b2c409fa76bdfd51322624a01b2ed69745a876ea3f47899d34387975581ad08097041f782c7a2dfdc7580368feca6deac99f0228325b0f5aca0755677c1512068d22b95e6b789525d141a246f5ca04e6e6af56193c0e8316b31676234e3d95be08abf2d3ab3aade6743715aad71386494f5e86c923ee6cfc494641ca73cec121686893d5d61a40e98e42fa83491983e6d87c2114af5066004481e856a3b4969f4ae6d7a9f357b6900f78dc664f2a167a65bb8fc914daf2c5d3ac55f4ad5896ec8387622be9c1b29e407a6d53d43dd08f6e4d8e2cd993a07209a3ee6838b6b9991cf4a2601ba3ad24f341a4d79a2d4f9ba418bade3fcdfa28b44b16fa7cfac3c3673eaf63f9bf983cf0442d518fb1d94f931686f7cd68ac9e1504035f8ce4391d4b476ee515191dfefd9ab84beed6ef0b20355b66e52b149a7749253c71dbbbfe4e1c4764e5a3e674f6a116106099fa22c9260bbdd37fc7091909b373a6462b5ea3f522c8cb153b6be24476761de4f0021bfdc68871a5214bf1bc0f1bea316c8406abb6a39aad533171ca52c6e6899c28e721bc12176cbd10ad98f91340dffb15abc6f8ec4a23e05050325044282b5bbffece2ad45738bde1dad4b77388024ea870e054c89fa183e2a79544155837db96481bc9034a3bae04931dbb77dc3835e1dbe8f438e11ce81870cb1e232bd54a232c14b86eb6a429fb611da926884c8e1e5589f0b572308e0163d954446cfb9bebcaea6b2604a1b126190b3ce4e625d32fd2ec655a3fe1345566c532b653c7d1d8c7f755736f0d23530ba2f7614dbed442ff32c520208b37a31dae295e8eb72eaecbb7f75e06c18fa1dc04c3a2cc356b5215dc2efaca1a977a37f234a33129718624d14307134a11af9ffd04bb3f05e39ded3e7d001bbc6dadac2af8dff8f0ecf768a253f27b5dd7e4a724621d6ee8fa0b67e171eab96d9ec9b3c23df29fbdab740ed637e88cbae6b2aa5dfaffbb23452020a42cc9c5d6afac5fcbd7b9c447105e4e1b935b9dbe63523879691efc2b702e19caabbd5e2872d5563be5a972001828dfeb85a53d0bd520b453454bc287217ac8eac804a3291c743c2f272b0c27d6e2fc68d40957f0a56f60befdc8b68876b041ee50e535987c2c685048346d1dc54861f5d98d20d8685adbe2f1b217596666864b8d21c5e2900bc63799fb779e214c88553fd6598b5408fd2e87c0d006d5469694901804030ca82b30863a17dd3892bd4ac9e951c719afc026e95362f12552206cc91a022ef150faf925fd869a9306cc1f0b8ffad1356087308e2ffc5fc0ee1db91ada96f30c895c067eab0abc082d800c20d1cd1736df0c81d20fcb9ee561acc5df31129b8fa248506a04decbd0babf8fea984f7a87a451bc880d1d2d8c12d39c2ad5d14b9493a12b69428e8ef97f94f761066cd97dbd9f684fa181aab54dbe5f0362ac623ef01e5e54b529c4e5754179e8317e197ad6fe9cbefa84ac9b967136ccee68bf136dcf36a4ef501ca5bbebee66534ad5d49aefcd49b0d582d496f8fab9955071f3e622f0e4105d89d8c5e2d84b4945b0144a2b8028d46c962a168fb9b9c78c34664eca7e1a45fe96cb0e81dfab831cbdbe11c487c47b27de4feb5689221ba64611feefd36a7db111070cbb1cc0d460605750a91b4e42fad095853545deb19107f2d11c18d9f80d5300095053943f3cc44f60b4c8c4221b15fc6fe802a14c066430027bbc8b999ac180293c2ddb6e3f7f4dc4e9ef74c20c0f24d7dcc2938297cc0b7f15583b79c63e72783890dce6d302be22e9ec865fd1f009cbd3657feebda6ddcad3bbd5da76d768e02259a294d8ca6a9258ca4737f313df62fce9ba84dc96d2c8c20a5f3328b1aa45e1ec61776ce44d7974864061a67182240d09fd2aac7e904c8ab4339a6ac216a83036f25e7285a189654dc034b3eb4e3080ff0fbcfe6ea39ff2fcaa9fda2759053c1c783e3127af4c377eb547b87fd0b8fece7344bc5cf0cc307b8190d3e4fb536fbfd576be79a867a716d347865de791b3e667a1312f62408e29467f58580390085deef49660af5d09d160617479cf470cc30ba56c009b080999126577b5a459d14cd115178e9f55f884a7f5d310d2c8764e3ab45526bbb46fc1f650a05c28ec1a362c23d246c245bebc1d64a69d5a8afa3f68eeacf845a048006b8b65fcc3baa68dbc1808c8c3c57bc1e98ee04d426bc5a19391a25d109d7395c00b841e5a156d0cf9dc1eae52d39e59e78d86a8029f7508ac637b304fc0ff39e4d853b46aa8dd0c687977d9a9186f6a079b02e4f6de6fb8c0c289332bc7c639a937434c6c348b907771732b3027a4f3835f2234968d427d65e319e9d39c590e2e93a0a02745814dd7284f7f343e285e3c2d440330ed478ff6d6c41822e7694071875af11976943b78ed917fe891a258b35c4131bcdf04e2d699fca49352f2f415adeaf24c6bb2b5180dc0bfa05c09432e02cc884477b479965a210a2dca0ceaef3a7e45142aec78aad13d3d56e7e8fdade076e71b4554fe695fc69063f139adcb986715a8102cbe159ab8141cde76c65e2b427193dcb5f8c81313dddb005af15cbf08bce1f8b0f2573e7c98b1bdf2da4990831e19a06a74dca3e3b882627e9b66de26c88045ef0db969313fe355898d90824283883474dcaebdb9b26da668d8f5270d085559ab283043a1a89fff2543031edda32e29dd3f80874f72f4d77080555108bc62f5c7201b9a849be733d69c2f6ddb02097bc148309801bb1d6e51211a954c1687f25f103f64577eb96dde517cbc8669caad7d02f804c9a2b597f65b630b9b28fbcaee54b23310d20b9223e261aed849e6dc2363443dadfa519ad054726238f61a05495cd61a8e6757ce13966c7148c073aac248eb05403809545d84f79f2cbf49e87cd84a985cb80fac89949bd9849aeaa73eae91a45a4933fd035694f7477a24d5345b1e37bc6db4dd765995eb6b857cb55fcf8097fa48d36001da6c35e16d1d3f9c9455287ed93657c077114794b048cf6f542e23ea526aaaa9d7e393b642b197bb0a33a886b23ca5a0e7488b7676e7f34890dce87258befbb4884e5fe13bffc80268926a8ef616be82e96d9fb64050ea49a7f2c5b0f4a66f45f5828180f9acfba84d009e2fa37ba9a108eb13e1d41593b9b1cd4a60a264d901a8332b80ffe683b31b92091e4cde6003a0af031aa94ab68875a5cf4748004d025e1d21b3f849cfc62d09e0668005e4dc9a43af5e9ac3427300b05c1b5477f725bc4169573c6574df3f2847bdefe18d7dfd35e5c045009e9b47fed06238780041d26fc09728360b6b08f38e099df72322c98c51091d10e82ad848fbc4731909def09b82217d43c2d9e23e4d0fadd710b32f9c0ed7917ac0b59cd8604161b6fce67e9fbe09932aa3390ce65b4e4ad46b4cc79c05f5c7ea3458d8aa19c6c51c9c9bfdf60ac140fecbcf9b0d7c2dc9fdfc6b8d3914a1f48543952ae4fd636ea2012ef8f9d3a348a89e407b96a70feb584af7d1b6495298a523d12b276e337317ac6eb6098dbd133e155c7f9b07aa91fa48e129ed7b2184b475a3857c40a9361f6e3e3b2f82ddcdb95f1b305176436d5d471e4c2105caa10173b5cf3ffd73a0fd59274a90d8f091c842c905faf983e8984ce263e36c6b2f5541fd457b326a81b859883a8dd59c942a2cf0973534a14540fadf590307f738210b99eb8d6ed70d95452320169d15d41296e943836c416b7a3ea6125b8d0131f45fbce6d5b8c05e7286b185b201cf256a6a0f6a0dbf496ece5732e45db5c966f38690fc7f734fa6519798ad858c13c6562f762e4be5cba55868b29d5457e70e7b846535c04c165eff2b81723176794a3e5e72cd260156016b217e37063354525426d02a40e4d6b9b86a91de2b3a7f2a18df9e16cfb813e5a288a855fcaff618bfe8abd2792ce1c94c0a4a26bbb40a6d394338de91593cc6c12a2211da86cd1eb6676a3597946bf45403b806bacdcadac6b8ea20c470c04216bf0841d6fba52d0435ec9788e5eac2b64ab3979d0674af07f90df42f8a20fdd3b8cdeb79c32aefde1394c506a3a3b7c069a63b18a68339096878ae6edcaaf783819a6496d52bbb05d1c89698420e333504a90ece17672eec506f85c85d03f1459d6f55fbbc4e9299f9cdb08d5cfd1c71267c4d75e55838fd582a61ebeeebe24ee8a1a66858fbac1632f38b3f2b1eb2aee53304d662b69e882a19c59c23f218bf4924bd36d0a90a7061d027b68e19b76b83e50fe3fd83cbdd63183e48bcf137aaa8e2a3d760e5a7ef2652bc58f2a7672016070b2e807609e35a637a42be75b11c0c4dd885e7c01d5b5846ec5d1d45f4f89a408b2c63c23e87e5fc6253932c450c980f5a35cab1b04caba3692ed64fbe897f06c93a081648ab54db3f44fd6a4af71a54d0ffbf7c8c74053d8cc7cf7428f825883bdb0602e2464d54b2938e88ea89a1777209a540b038f6d449150be68684618492f7f4ddf77d66f1115f8e7b4c7068f386fbc63311081d929f3491d3a2ea8e02a91a509a092cc88cc29d5359cf3e1f2ea941837bd491fc263abb7f0dc78e39164aad20ffa7c7ad957cffd416a59103cec98cb7c15b62939b2abf74bc6d5832f3494f752ed3f46536fec68bbabff343d50ba1b7d58d43a66688fdaeabf9bd2398beef525f06a4cc5185d7c90e861202536275ecc9b912b2ee51fe05e98db159a4d916b28c293c5b21ee9f81533fe2b51b29e32aefe2e70a0d590bef4d3277407626a2ba991a3a9ded6c28474dd4ffb0a2bd00138679480b45de3fff7c7f2c15d13b459884ea34de34e19e9736f916f6665be8d76bdc54cba22d1ef7904c28100ede57c01324f195e4b39a3ca957f0729e881e4ee3b672266c7cc3f3dafd37b9690e7ebdc18f22edda5c250f1a451f66f91df9519cad54bcc8f4ee429f13ef1b0604b04a7c7e6bbcf58d139ea376c5b46c14e57700e82e5e079c55c690410bb0f6de55cac7735254f7e69710cb9ff7b61f372315a0131ec016121f11292b7d6dac429fa3124f12d186507192cd739e2d1c5d36cc447baa441588818ba2b5b65e195324523df34849ed355cc03c2974e1d927491e3de7134a4f94ffbaadf2b799b641e85ec90a225cdc7cf2f72db5823932a9166ea86d5097472d87d8fc918c5aab678461ee4004dda5e7534a5cdbd678a3c3f8acd511228b1a4baeaaa6411eb2d8251cad442926b32763b31b40890d092cb850299bc1aa9fe3f0d5aa5d2aabb5dfdd9f27c601642f1aec962c3d4def230beb41d861a0b93e7c6fa0230b4d388080abf6a4ae80568f91f4d0006fa1ea9924ca948824634ffdbb4785a35e73b2dd620be07560d3bc01db686d33a979a4b0405965ff73c351f1cffacda4ab89f9a62b5fc7d552b3bda1a156eaa3a363798b83d513ca34d47011eb24b73ba5c2bd4fc1eccf8653ce874f513a6f1bf8348644beb994876dba0aeef1981c10160d4cd89f235d80ef5f4da0b8c129098758288d1e07b0efab9cb20eae6b6682b42dc62206f26e56395f3e181bf877f9a42dccd2849373ecfda91ae7ee84cf67d8ce3d3e895b70d91a0355160e52f4fa95b0c55d99f0f5bc1116e21f0186cdb64975054de9ea5be5533a6b892afdba78820e711070f74f205d5f31bc7db0f4dcae28e1cf176f6dcde54785dd5f9454506662aeb2ffc13347634301959febca3dd1473df3a2b1059daa856e27a1a8cf57277e453e1e45bb544cbbf43c71c95bacffec68f1fe17d3588462e45d415f137cf587d6cf0cc949cbe7706fa4a35276d9199295b75c2985b7cfed6e9a8685fe1fa9f051d9898b80452394da59353833a4e0d1a9837f0ac57eb690c0c69ac5de8a957fa4bed7da5377961881afb75bb467c324f91773a299549eafd7f05a7093f6f291da18060178fed0e8a290572526fb9c4d04458656b1b63fb67fdc995bafa39d53c3e34373c936689d4a1e401d88f28ef40471861df7b343dad0849ada6d46b73faf6f2c58ab71fe08d56b5a7fe81fe1594ae7e0e4dbc412a1bc81ed5eb5755f0e688532eb53db56501e9081d7b58434dce856c1f9628fa7aed0b27c301cdf920c8b1aa3b7ed80c545148bd7b57a3929bca33f39d9d30478c5aca0306ebbb8a060012230444093aead32c784fffff1585bf42d183ee6750e28859ab11000828b88cd1490141ecd6904fb27c3140f97df8403a2bf97f69470fc57260f92cbc0954eab8da6a21757cb4fe468ddfee9a474b9b36f1377379ad764ea62be83f99546d3b60e6ad4ad274ab6a35bbf04aabd54a77c8f8c95c2bdf8d8374b905c0e6a60117c2723da3e09d848fd91ce63f4b96004a13405f89e354364c4f4ac882228dcee073758e8de1b611b4b8407247db83f864b01672d8486303c4fb4777c6f6ad7b2468e8687b47d4dd89ecc1cd6a61dc2f53b46249259e09f1ddb85bef6fda40d820d43c48a8b9d44f90388b477d9b5f66d49f5e75bf676d8fea8588c455bbbe7303389aa27f5cb4b088a0091ccba1c2825f43b6c15fe572f058afd9a71c8392a9350dac5471f04103b5ad92656ad2f6d341a7fb66d6ade780a6a57b685a152a16b1c2697a06336c32e489591fa36a526ad92bb1c17f72012a56dfd0c049346d3f865e683a000559aa397e5216c8bc728042e807fe2191fe18c8b49f6a9bb2d2f29d865e3d3dfb7881166d65aea48c0ce5bf8b7f7191d44df81214a61dcf548383921d12f7cff356ad0e00a0ec3197a1d5d1264a669549fe7f8ce77c61a152843c17b1826fbc0a991c268583d415a6042cb06af04d4b8e5814717f1dc7cceec0a0cf352c6fd29ed608d0b84fb1fe1f4d79c8018daa62d9dcc1ad966c3f76491bc4f7d85a2cd0cb80954b9e1ba0cfb1aef1a9da735439fe320b3b64d5625a2fcb88bcd2a89033091a1f21b98cf71388a92403e602cf022faf316d48d056885e363ec064d481fe8330d1b18bcc64f32aaa9b1ceaed05946ea11cb38a4e61a0bb62840c42c5bef56dd0041bd7169a2bfbffee718edd3b58b88d9c647079cc4877dafa69a8bd43807997701200eb9989f52d24d77b7e4130ded5dabb47a8fd61ab67f14dd4b01783383b6d3763d2a009fa348e588201143aa085644a14b09d5acb05fd7be36ccfbab9abe5ed1a75033dec8bce4f259df4383829845c2ca38e3bcbb9be8ecd2e188162628734125b0eacb30115b9e42dd8658693a6dac0a3020c3fbc0839bb1fd1ae5dff1eb576decbc45a4ca73ca65f3f541589761c31f716c142dc01cf8066001d48e9a7e38967cc0eeab6223cfa76a562c41f7551899773bf7e73a5aceb765e84754e41c2cb16c76b43b19ff8c5bd4eeaedb515e1a1584e537fe921421022e3268128a73bc069fca9ce5ce80a32225a8f7ad0de30866af98b3ca6ad7a1ae0137cabf4c39cd1337e427d77414a2678c441783c007c438424d83793b2a241451f988135440d747c6a14bd4b30e3cf45fd49ed7d73de18a7423a264e4a73f6ebca262939bfe9a0c11eb4c4e090bf0715654d7be80a163a149b2e82d0d31b8f4c75a2bd357ee7d2dfe63d29215a1f94c791fe2b15b65a353f48a548497a2e643962927315a1a663b915114d622f1bae1bf0dab19a4c6556c60f844bd59951fef4119508338e1d4f9199134f259366c6c98ea45221a44ce203ce3b62b4941753503516aaade1539b31940c856743d3d132d6f091f599b483800ba6ff5542719b1209e846a8f0e8642db946260255e8632a8125cbd19a7e7c511c8dc7b6826b6ab410013d40685600588f6307cfc8613a5cd46153f91e22332f3681d25668d8f0783a19d42d6e773a6a0a57bf408e4cddd80884e7a684ab269908b8585d3e4af60c3269cb34fa57c86b147977c5897ae104cd00502dd1eceaeb7fc5df62bab4798304cb46a6abaaa838fb6a9907d341cedcbe0fce40ae0b3982e576d5cacd46ca5be5398b7181f9111bb461198d182a836e81f35b4aaf8bcf3436d65ab9ba11711aea175648eecd9e6c4668d8e3719ab213a15a1f57cc63dd078efb3f4493fdfa9d36990ccadc8cc03dc1d077fae159605b5e1c18120034993f994cbfc3a358c46dd853478927be5ceda962044eaed5b11dda499caf5912a4e215546833794e775b252f9d300d2870efd45244f143f6f31dcdebda3047c8cc645ebb773d1bb8b84af422c25092f1bc8989fce65096547d5b0290ccc3c4f7dbc3cb46e690e26bceb53e086b63aa10435cb89838891f006661ab0c1bb4273f1e06c4f7b1bd0d40349c63c81f3a0a3384ddf9e656b867bbe5c9a73c2a0dc67bf2b36a4b6b86e9aed74b7e7a151c2bca8e1ecd8fcbc690f7e81302889747c10f2c29a1f5a60c9ab0f7bed0bee7ddc3d5f0ff4734bbf0fff3d13530e2cd1b8e79a4450f1e52412b0dbbcb441224ec51cbc77c6f61ea4f15bce77a5379e9efff9bb4cfc72468bef1fd6366d9b175e65e07ee5fee46ce71e873f3e5df66d5a94c0a3d03fea41d8ce923a637e48b383de172bef08e672b9f75f1bc380510e510eef5453bb33e9d9ebd119c4d4c308efbb28db15bcb2e595770e426bc50c78a60e2e65d03de927261e55a57b969326d1bffae0bf75129cd0f3b6d0f0d82005f8424d593e5b0834f91adb0db8f7a73771784b5349cc75a57216ae65d3a7a512e5d486b036f1232e2e7423eed138acf93b22606fd2a8ba25cb7956f998069b5586881bccbf5b46fa6e3bbda9c43c366dccfda1e3551340af163f6914e1d80c0db658c9e4066436db6bbd8375972dde9bc10fab56ecc8ea8a387191de7709be4997c5337b065f5a95f7d62e04b691ad4206e6fa771f1353e420ade16f6ea076904e411f5cb1d2570d75f5550006e347e1a2a1761556e43b71b963435afa538ea83e40366ae51a4e4fddfef91bb305300e192a31dff9a63fdfc2e265a433edc30e5134a86aecee4bb715bb9385f1cc7d6c82bcf65e642bd5a8998f57aefe4131ad93207bf54692e0c640021727097d6785bb1c718ba8862433fad253de680aefb451cdfb95ff3b2bce7ec423c0ebafdf4cf9df040d4efd996a9ab050ea7581f482badf859e151a14bb3ef848ef46fecb3436b0559425fdd297b486b15ec4b934d2b482773cbb797c724290f22b28523e2e4a155c1c06d98abb9d6f99b1e8c0873a712675af6ed1fd6a60cd0ef76c67c4032d339831fe1d8cf0f8eb08471db46a174a30fca295bd6530d8260da47d7f443af990a82d853a49d81df011a71b0582c13c98029f0087faf110ee0e17e2b04b00ab0b5d7b6624aa43acd8bfe598180cd9ea2c17a4c0b5b37528abf2bcd7882f819b37987f0a71386cd7211a96843c86bef4801dbc62a834446f83a3b0db37e66a365dc95e9651b875a8e4eb5979a4f012b8a4a7cdafeae76430798c7c3238b51db733f336b4290dee021219ea731cbfbd17e35a13d7dbf1566738cfb79bd472f4c4a3e55ba388a50c51a148f9a419cd9cd18184386574010b191f7b83b1c91e1fce8a211a1fd2bd66401c1ea33bd755ade11961b8193699b6013a69c95f9c5d7ba91aeef41f59cb1e742d0f05981b7f830ea256c1bf946eb77e1230244d3e128451a752c3fdf7c034f7df14312dc0356bb2044dcfce1e6b65f59491898400b6b1a39f1876478a9f59d580157c93d1104e423db2eed99b6defcf4eb116e2f274c97d2c7374fb9e9811a93373cda725aef5e45254b2dcf14607bc8babfec67d68f7aa4948599dcfb40cfc736c5e5839cfb15ed9b4cdc5a0d907c0110ebe87a34ec37a781c7028e77e36e5caa2e377eb8ec1ba0afc2a9dfc5ead074be1debc0bd1eccda46208c62f321b1c5a387bf74c70de90e843cf8d0ab1367d2b73e477f6d483130db6d4690da330a94590b94f8bc1df71aae0808c73ea09f16a03addd65bf30411ae04b1a0e429af24057ed1e904e3518fa972d438787253ce32b657d1b5d6cd97b74e3a312c74d02be859b615055ebafa2610b016b8edbf00d0e230d31e5ba560f18e3ad85bcc605ed54475b1f1c499c60357dfacfff19777eb33bdcdec5cab115ecdd967ff44675019c3ce4354242fc2e5dcf3e0306bd87dadac807dfdedd645d24839899f64d45fa07e6d4ad61081dda626dae218b0caaebf8916c04c24fcb769879b5123fc02fe41dd72de7faaf225b73f42882edd484d3b4ea9ad319d922a44385c5c52f0615574d9fad3e4d6c35514ac025dfed0b703a4766db1d60ff820bf40a00d4c17c35953b8a1cb2db5a2876a805e975ea045b9e1feb1ca7119be2c007ccd35fd5e224f90da92118d452b96fa9dd6e1defd5adb481299490cebae04d7e9a5c2e19038f65042a835839124503f516fc6fff5547174ed70702033c7a10d8fbf6ead965ac6bf88d100cb56c056179c0629036c650aa279eb045256a799762fd3ee184aec82ebee0f0eb2e5cedcab33bc59b10dc899b4242050736199850e4818625a46cbc00a06e8bd499a00fc5ff5633db3f20fff71b1e63e6b3bed1fe6d36f79a5604fa8311eb345a278f01d63915fa05eafd87782c9246a79a3cd1578a1aa625b0317f858dcbea41a07727c41f504f74aa250a66b2ce1e30b913ef8e8d2f48ea6bb68716450e79cb9e8e51326635fcd3f31c790b03e12b1ba222487668dca3a123d53bf6534dd804dd6f5f3d292f215c6efad56c298482404c167181c786bf2c08419ba4af15a8320b1424d8b6527b0caf158b7dcf06b869fb4806eb8d52d7fe56193fdc8b5f7e034f9f8b5445dc1e4f28e08bb560b2d341113acb4014a645456bfb5bd5f7110f740b1ca87bc59510ba887c7986054a68611cadf5e5d8c3d4cc06287a1db5ed3feaab535bb67ff2e94693287265b46e3f6995f309f6cf6bf74353e0aff4f57ab7fe7b3880cf51276d37b3a11aaf235b09ce4cdfc3d374c851875c76b508fc3d081d76259a733285439694037b22e2e7b7305051aa1d4ab63fadb3f0f380d299d3f84ea31149a33c614dfb859b8b162f05d7e6ff4a33479088ad2f20ed5098e28789cb30d74abd86dca92c13769fd81b3839aa9c5052098059f8aeadaff5a0ac6b9e17e5d85b3ce6b689bb768055fb338e78278f8d7645f77a2bfd30205482f4ae8cc1e033fd374dc2e663cf69b56801c010989ebadfc45f0466137aa6e623033993f499de2da7565f467c99ce32d13a3b6a412f2ae33b77077e5c40517c35b865d4365e27bc3cc637ad882c15e9e8693300d0cf37e90cb69582ecb71559b6f72363bd7b3b93261db6dff39a7a8ca16019dbba04af4742f3369c99546c22f7c7ad19d70ace03b5036704b270e6cd0d405ffcc833c78f8824c9f33b93652c130fde7fedf835f468e5c0972986f984004f96f86f8d7ff499400c04b132bdd4e48ad0949ffa94c8848fccaf3564d864138146ca99180933dbd1b384303c3918a37a2e0d1dc25a220d5aae4f0ae52b2270212de09445408388d9b89a2b7a3016e8dcaec118a4c9e8bd7b671026f469b0bbfface87be95b13f0596f0d1aabb67fdd9e21e075762ba5563a5c83a08b6bf82b2db56d0cff78294a4a6bc9049939ab10af74e14b13d031b72bf92bdc95a532ec7a3d78fa398fe68cc0cfb1f38d5f22725c1beb2684f52482ced94611bddde1786bde5fdc8e3f4a9c3f3c829f56ecfec779471d521126ada1e9ad63adad95460cfca0f31d9b19d46a175a42106b1715d094522f65018cae5ba112583443fafa4c7913145b5233c006194bd573a0370d74cbca10b7f0ffb01b3b3717e08a198deef603b6e942553503a4fa0a59debbbba04fe2d274440e17f9b461471bfc571424cf785f20b36214746bc3ef94ba4022f2a6e7797446067e7f10ca2942993085f223e3855b22b176f8141d5589ca509712bb5597a1e199e7ff11d1443ad48993a7aecbb0e273e2c22d4fb7c8df41e0f4bca83dfe52ce57d6dfdcfb1f0ed69168514d5039b4b42d445091a5a83d373dcfe37a900f719c7664e62edb406b6c0701e9de40452729aac8445cc47e28072320dd2963e100af51bb54c15e6c3c880cebe24e3e001429f4ed957b5a4773c9d1eee3d08f23cc95168ffd50e4f4cce72c62c2bbdc70adad54361b8770ef005fd9214fc408a22d84392137af27acce7c09f0bc3e1f27c85436f08801e794e8b1fd1dae1718adfff286f8b5e09c605a6c1650090b8e1c9eae8f5fbcbdb0f0c7a5c242f6b4d611008583e6e57fce2cff747a923c1eb4d806e0e15a19f4932aa16b8441f43a69ba5c662f4f2e9a4409fc21765bb4f522ef65fcbcf0b4eadb5fd16cbf2f648ddf09244b41dc8e2b2ee422f04bedbc63875132deec04fa7a9458df97eef4d6adafab6ebb6539f7d59647498e50fc837543ed9f6251d07b6b78debd991af568593f7cdfe3a15bbdece740fa82e4ee674846ff8b04e571fededa8aeaa2778624eb330fb0f136a98b42c818d47846e1cbe9001dc7390235ad7dc1444e1fbebcb5f07fe9068ae1c17c29521b933307c50da1ce581761b35f9e57b0937ebb32f476964b15c22f0ad64e8d04489a2f29281e9fd1af288898fc980982844acf28defcc643ceee386f29d045ba1089af68243915e2dbfd7d1b93ff8f7a28f357bce2383683134b4e08f4449577366cb45dd83b1c99fdd09da2c86c03f00201d9fb162d604b4bc376b7465fde151501fd0a22d57c745811c1a2f79e0ee37a1c4d455c0c6b425c14fe243c5273ee9c4c7fda8d86bb40a23a3085b7e0983ead97cd4a8cb9383a6a551c1b0b994cedfe94ab154095affe81ccb8ee803a8530b34dbd40b043618ba999bd26a7dd3061443fca915d1c6ebae36200c0cbcf466e6d2ac842033963b8232c34446f5b5db7e95c67421ced9349916b9b1b86ddba40abe84c9fa8edda0b01babe9c5fe38676ad9d19a88e1066db154d075c3d7e207d341b20d7ab180f9b4f87fb1a805ac5ea7c342569f27336ab9d51e31cd3775a7bbf6c72d999cc41147ed2c9a0e8b5d48e7735d3d4c1936f7ce5ea9ca8dda90b24b3413111f860739a1bd47e51e82701291e84731451aeb70605ad1e63f2706f96bdd78cb989980b32895f090f9292315e575ef171a3c1db1b57707d9b92b523b6a2ab0175535db35f3131f58890729d4303af880e84f3f003866a39140947e9141b6f243ab18143ba23c4710859727578837d542f2b345fa84dbdd69265231dfbb905dbf5a54101c657a590da7c92868d55af26cb951d07de0c95610d8e170418731ff2207bc65a4f5a0d0147faa99e7eecac8e9385ee4a2cc57f696b41ef1d9efe35d55ba324fe2ac0632bf321876116ea127c6b07cf4932d92b8744f9002c1fb078264c8294a3ec8b22aa45ed9bfa40d7b8c0cd60d25cf66a6fed08d8c0d4b301dfd873f106c4fdafca18ccf0196b36705f226ac8205549bf6f53ed14cc3b75e0365c0a94ee93fdcd1d7dcd66c9ac7e64f62d35d3da8b5877d7b9709b87fbb584fbadccd198193de69a7d7509e62992af432062b376a13b647a2b3542ad2c693d5a1f79f081c25176ed3d5c54cdbada0a11068efe782fd8453c1f9da66dd3b3f8a98fd14ecd269821e9a08bcfaeb54fc4cd242d3d1de1d60c5295ffc82e4783aa439406b19a4be50066b9f9b811dbd79a8b8bbcc5e65d5dc09fd96719d4b61d54655aee18cb695d6f0416be567be1f07171f2e18a0c369cdfa54597649f46715fad2c23ae38561a0e9dedb80c12c7f2d27983d6bb9189dea069cd5a59a5035fd5dd1f7ac95fa96d1ac530ccf089e10fc96d932f2df513660836466fef94ef7983577e33f92a79b185af2285cb42b5d514a894d05c32635dfe208a26dd25084033993400e6871e47399c154d7497c3b1a1257118f555e2f79ec030a19fb17bcd1e6c04518c75123234b6b505a3127ea05489f3907c7f61a90972c8db9f54ba26d5cb4ba3807ce230675f0359f40a61fab5877dbf7cda531d98c8b70a7a3d27169a5d81c709de90f18b80b5f9a191e60eb6f85f3786207cbc0ac720e100ca8ba3a678023651ae0b7edb1e300f26ca1f043ffc7a34a01dd5eb576f33a35d85e272199ac85fd5c660f17fb45dd2eda43887c41d4db081cc54bcca76cd0e041c563ad9650402e22aab1e168ecda1dc0b51b52ecd65fb1adda881715e80cfe2a34595ccab810f349ae7f95aa3cee8b9c9d1de710ea819272c65b51613eff064bf1530ba9875741387d135f6d66cfdd5407e5b11e86f1c5be62a0ef9cf58a03f18764a382ca8aa3315867588f211e2f6c841a4c0cff07cc6b39af5d0ce22a97058ad3b1eec2478fee16a4b9e02717b72eab4a20c37fee9f4678a6e40df9e7b00f2207870022aef968a0d3fb231e0d58094dd0ac333255ac9ced264b9b7e3d895d0c2f6df80a97e3c676df2fd6874f4822c989c7c1057b7b2420f12c5e75d0e9fc50d2badb5683d16d85e878cb836803a2555601f721ec8423df5c0539dd00846321d6a90d1ee44c38ec6e8fb9c2e4682bb2d3e818108ad8324af176c1e1db74df5295c6a58b5904e0acbbd0ef54200b3d922d2f1824b546b5bd110750d849f078fc0baa61d7f0f12c6d58b9168d61d3ec4caa1098c6510947675f67c5090c50805a06039c8074c220fb0c59b59c1c363ae02bbbdaff024c7b0bdae210ff5cfbc26c8f442f98314f5338bbf4a2b52eb926ec2f30636ffeea0df795f0e5e0427f9197fe4edbb14a66545cfd7b5b2bffea4552db09f1a379d36ffca5cffe60346626e0796abf65378506992be315eecbcad4649d5886c7b9ca8a842d396b976d2c883438c1087576ae92c68342f86d082dd16caf8b8866228accc251942736cc9bfe110aea0f07d0b2d76bfb732da68090ae453d14932c9dd71edcbb392f4c0b3efc82796cf2f5d2c885c31f7093b5f80f12c38a5bd724a8400e8a4346cc7f80b7c4fd499916e6284a2bed16390f1b2a22263329676d65236b8159ec3b41ec1c00e5eb96ea5881fd1e5228866c1a5be1f0af99dd5ad82f2fcfa611371d8a421678b549f8830950ddd58b6a96ab4ba216f14585830a78783ea3136afa3157872ca34750767984fe2378e25ac0d01fa5014f55682eff531a863ef0691dd29054952156054c331164cacbba8d7b8da07158b93d1db540cf90c547d06b3e9e2fe22f490c9f591921b805c9b0e793d93acb3f2a1c950668020d824b6f526b5fdb4a0482463fd32004bce0be75b2e1ac1d52be16ff10f873b24d11bde5abcc0a391fac14aff47d19fd69f093105e46361808b5065ca15de6794d418e54ee8e2928cedacc1a2eb8086a83f5a43699a6307c2d11d98b6cd91a5f6b692f365e4e18e430ac9df87594ff0a917fd8a7ae7289bc4d2e35e8284976ed3c44b4900e8cbb36a4ff7228c7fa544709f973109c177b25681cb316dcb2f822decb92741609e88cc0c6c817b4ae30343943ca76efe28d50d1585f3dc620f78e9204154b7ebbdbc5c066554e3332d2b5b85c1a6f85ff27b0de55e2bf1b08bbb4d48bfacb76ccc918d589f7bc45750bf7038947062dc652c9326c560e2cd9f99c516dbdef12eb01a3c37a78c92ababd15b4544f608fcbd266946fdb74e3fc53f2710565be21a4994f476207ef7a061c2a1637d969853119e7e73f31962d6da681169004ce1597846e67ee43b1e3722e5bf98fb6d53de841ab3b8d671d06b77ed20493dac5bdfb3655f41ff29c98eb1b2d1eaac882496fae1b2efc9053668c16727d1a83f4bb37db86b51d2f066461f0e6213720a55186b11f8b490870912fbcb789b1803d10183bdb7d8f2af27477f47f7339e6f0f982383eede56b30a8d59ed87b9b15986c3588b934e9e58916a0aeb914f4b29b24e67399a1b7f5610db58c6af081acbfcd5382cfd7a2b40eba2ea8bb4b3b4eb003972ac70e0b9e855d1b4f45672c6582cc40ce03a69b3d8829f629f7f39df692fb9f27f60a5e069948c7dd5c29672edf147fc71e1eaf995198c5da57a93d7cacc53983cac04c619b8cd6b385a75aaf2ca3970de7ca6486d8ef8cc1eb7dbd3123c3f1a25e2bae706e131ec668f85d360d75819f9c8d8d0ef973153f11863e0fac49b0e99b431d419c54187da05a7c7955f067d69125689658af6bf7c77b92c9d1e0f0efaca03e113f7edfe962d0a54421ad7708cb3cd61d9820b08d7959158732b3199bd62bb6c99ca69017b0e1da33622f25a14d2517b5e389cfddedbdf428cbe0b3cb204a6f104ec3bef7a9f798b1e14f6f0e9b3476af578f98060d8bc380948a37a6dcdc39971f778dcbe7b81be5583c270f0b5540f973608815cb71ac26b71b18b957ff550e202469cbe002cf7c5bb6ea58bac43189f0c355801c58805d0a0751e3df717207d195c6623cc7c1e557ff2e240964eff0ff0684f0010533b1740331e065e1364baa4975e1328e953cfe4d2fde1fb360e6e527806502638c1897a9f12b4980acbe1a5bc9a87646527d7f4bd0e03137cdbf4a2182f5d2d5460695a4ca49ea81976765ad44cc9cf3b5e9a8067b697a5be6feb91209a3496616512934f85a844cfebd29906df92d25e9fb4f87361d0f52725d6bce283e3ce163da0d09cb7e2aa7fadcb1c2051b3845d912253c5da5870e6f9e2cf5c75d5799a3f09a7cd50ac74b4b3c6a49760caa82f300d8a308015196d355e3084031591ac9d726c5d614b5562ac6951d1ecce71ed8644bd89a140ddac22e0845e4c38681703009d9c1d1186c6343b986ca2ed2c64077c28f9dad4ae8703e20faccfedbf46966c967c2915e557e41f870c16ae44ef5dbab89089cd73c0405ff7c66308194825812b65692912a72eef63dbab04cb4184a4a3ba1e363d0703f6991ebfd80518cd5e80f556fd56ddced020a7ee65154befd4ac3a7ed505f142721a01ec50fa2a6c21f70e60a257419932e8fd6f3232ae8192f0a46e741b9da4f12f5f5b98064722358901448eda4d30b896a809a688474dd9726618a3432eda64dcf4b9629d1524d87d4ed438c6860e1591078626f727edefca62b83758807411cdd67926320ce1d7b238ff0f33276cb89a217a6f65c8d65ab9aa6d081bbcb023d36b9767d6b2163567387ac740a56b9a7ff14cc8f6881cc305b6d8b5724ad69649a8640d6fdb665e79987468abf85fe328cc70c9680e08b96c01226ed0d5a960e2508d73cc4d256d7ad37c6f092eee4f2b5e6444ecb2d3ad635885af33f0497866fa01ee9892a979cb08a9aa360abb2aca900e86f408257d2c8b694d76082250ff5d6293bd1c3e573fac13ad483d3814d3ef74291d504e849f248cdfbb839c06fe5b3d3b9a88baeb0d19daaad465e2300f8dbdf2a90accfe00301bd6d64ffb7dd5b82b9893c3667f4160f4aadde36b6fee123301b46bced1372b36f35f644f0493f783a8b56f8266da023d32e2d19428e34f6e11a93fc1f8503bf8f92ab1daaaa460d1cc4dee2da06174275b1ccea153900d071c2fed0a847d81ae4dd62ca3ad9f9ef7c4bc36a34a1bbd4d8c5551bcbd56d2bf5976557993a5424ab94362fc7b7adcc71fa8316e4defe5dfcd2cedf91a7d8df99d02cebd2934498bcd1787b4d12605d13a125b6575a66dc66f18fac7f6233f9860c097bea8b6966cdc2e226c3d3f138bfe52c4b575fef8c0e2f5eb1fc756de6cc45fbf7baa557f8fe3c2aeb02d00345a3e9de0b62948461c8d46a568d5b6663717de49cf18718cda07cd9e3fcf40057abd906c7ea97d02cd3ee99584f674869e1a8078896e5a901176bb7384474738430e87784c380b912c75e5dbb8577e398cc270d02d012dbc05e6c4731a3a14a410bb5ee21d6fd5751815c87ce524af947918d7566953ffc0b82898e79054895a6e3eddda130f13dffe7d2ae87dbac004682fbf8b5c3089dcb30635fbf550c4b64b1922cd4a93bff58c11ecd48a474834854ca9daae53c993781b0672b65a35b6346ea379429765d3be3717580b693d30ac5cbcf9fecdb66651eb49f0174f3e1d235a0fbb4fbb144d8c029a844ef7a6fae1d558c83aa0a4341911dbfe20b6f386eb0b610de037e1108846e64b3e16d110ed18687fa5ae6102b52e789e1751fc3f557ac484901aa2ee502c813c45bb8dd684f0d0c82493231e026f79e13e55bb5fe2adef245cfefb7e733aa82cb05666ba11e3479a0b9c83efc424eecd4effa852947843ea817d044e14de7f243b955b46de813dd83615f32c9e2df8132932f95fe239d80bd633cb122aa2fd3d3c35c2e3bddc4e79fdd61b265c5965fba4280eda02e28e4d5485bd57b1e3479fa4980bc82830c75376d830ab974fbee4da0adaec623f3cffbad182988527280c8bc5caeda2a333cc3eaa83753083525a45e2b27f6b8a1944db890c4b80c4b160fc75505e9b7bf4beb032487cd23fb31ea098e37f939cc29d43af541eba6e347ffd47599e9b9aa755f880ca53d55411b7e980d36039cbd683b11892c9708a43a19ae8710f64b165a3d52283a0b38cece1084b22ecb353e17c6985732f1ccdce8e32a0db6fbde117e288a37872b2d408991223da771c324c0518d6812292baf519a8e95a820ed0096b08fb20d4e4c0f8db24f555dfa488a30667e9645ee06fb0f75ac894de17d1c2a4a8ab3dccb173fcbb50fb90d517d9fc674a1ba619c32d179127fa82b90ec02ea57a747ff2f517331d8b74d4dd3139ae9a9291e8775261fbf0c1498aae55e0e82948dbdd3b1d2e4b5614365858b01def82b4e018a6646ae2ddac42482b39cb025a2d625ae4d14d0fba41dc7d85854b3e7f0c5cf3b0b13b5b97b12a6cd7dbffa02b49aa533066eb5d97d2cf8f772612fbd5653b94bf8bd8536bd682102ebfe97e84622f562ab63dcf5b149325d81e937b655c4b0bd789110e71ffd99a296045f58251fa9945e74e9022735879d3f21e6b0640f839ea62210cb9fc6360af403552afe291b08be1c55a8c57e7a1b81829f41fb3e9c2e44f566fea723acff3af6e39e4beffa39a4ed587020ff361cfe1558b7427d16199e1653e7e5fbf6878b0b92e694516e8c491e8c9805e2344b477e3221726f3a1b6c8c060cae623a3880f20f475c8cd3a642658ee744bea68b524b6af6c852592f24efbc0de426493b840f16b56d0cd775e6ba9b752382a08969a4f8bb5d83e8e43b2fe359a3d7f9730397162fb2a55da399f4a01397df716cfb1080f124ec92c3b7ee3e54000f61419465de654f591cbe7595b7aeb8aa725162c96c23be000569bd3a8d79b94a1d1eb48df3fa1faa7e66f56dc5c9d97cda399fcdd80ad0962c5286e1d4aa9638cf30a70743041445c516143e686f86673b99ab0d8e26d831e9f82fb11116cbe77f765555ae6aabce3654961ffc475246bfbcaf1425a2a7d072f76498f50812ae471480c2321f60fd626ff26034250ac065e9525e47bcdcb49a5afd690dc53a93103a69bf4550bc4e8824e2b90a4290d258051f63365e581173d02b66b115af0d6e0ab82092cb7c8cece325b38732949025720bbbebfcb7b1e4e2844f33832b16595f8c26c5f8f2ab7bc41fcc11d9b4b4142eab83d68b0807e79ac4ee3c885ccd5df3a60997f24556d063c4a954e6b373d5ff50a8f951a64faa74e8fd7460f929d5bfd1ba73a6cd088ba47b7d506b61b0733b9ac4991fe9771767f5aa5e8cd0a32e277251423c0e3f38987952b381ccf9b306c1bc4ccce38b11db968bca2250c7d52be99f435d5561aa2b1749e0df302ecedee0d572028c9b916ec809936b10e383c15f0f8ea6ba5297887833f4b988236dcfc5c0ffcfc85394536a0e2d2465a32fd0f2936c61c78ca52cfb51934512645ad8e8fc3b0b4214ee6e173b454ec6d14ab60d5b69ecf14ed25ed8e2bc9d44a7cae3111a95a3f97334b2aed37b8ee04b1c63d3f9fe8091149452e74a6e57aa01c85d747449dcd11a3a691b0e0db80b69f68101cc8f4f1de5dba50046833c01ea0bfc70240625d3fe09d40bf86ae96c2d6d204dd8788db64de62d31afb5157669a6764583c623215e45dbf20f8a63397a1eb6a3ebaeefc962b04ef8633a32cbc828f376b9375c496fae6e77d8e9e7e547e67c2d835e4ca0c5a5ffd22732f30125fbfbd295189000b6e61a65fecc4e1893e04d87175c5cf85dc527009a24b9de14b3a63ac03dab36a08cb487c0f91df09bef0a8652ca3655eeb22d7de7b90728e8e73e3b130f625753580fa7516fa1258102f05d9cdb77fbff3853f8cc65665efd02a306c8bac216f87fdfce31e209c147422e6b9a1c55e7d1c0169bc700a353e2a66500039845774f76db5b02578672c36f2cf0b5af7ba0731ad518a81f1877e5fd345c8c613d79c66d83389c7527fba6149d5c429f733f66fb4788b1b504bfdd8da5ce97fbc5cb70418d55979da50ec8a8c3ea97c783bea20d6c87d73b8ef2e4c11ff3901d0911c5a119e9436a69c42e991f260a3cf38dafa4e31e264e523dd4947ecf79c2d907bf9734788d69114633bef9f1443937c4d48921891ae750b59dea0442cc83eedd64c2952b1655118e306fc657c9ae8bf3fa74b59bee01d65460b8c592fdafa9c9337e2a2aa1ab94b9421589e8054aa12ce4049334c9603f2f65f673ce3667839398c0438fc3ca0498f3f6e60ddb1cd4f88eb12bab1e9d83c574a7ea996010d678a7178c28478508401f5a2e5f221633603791f6febc3de2cd18ac1984ca28d5d225066556be652a1b8c3dedeab3996757dca2f6c9a50f3cbf008613c6f4c98ca006794717ff9c62fcc17abe60b239d9e6e917c7cf23932449f96ae3f9351a691ea92cea1a2096ad1e7ea1bfa87bc84b28cb3294e116d8da333ca27a50eef7c6952a488259c9209b8d8d130dd6fc03245ba0a1230e7cce4a1c338e8ac9a97b9b6c7ece6f51580edd29830aa62911c7d1c82be3b57c7013b8731ba8e3679ad2823abfe7e22ff50af28693a0372ae898e9868edbf30818fb8dda760fa0f3535831078d606739c811a0bc8b7318a5d3fc42d06d8e0fbc80defcdad2353aefa0ede9542ab6e71d31f2f16023945817715fa3d1b4c900a594ac9c69caf966d5cfc19d9c2d9ab73bb933818186905bd72cbfad823d4d5465f4e45bc02498713bb2c561cfee0d64a725b8d754e7507eb1723aee2e0135c740e84a90f8e0afaeb9a3914690b30249007c994c3b1c02b2d28d87547e209d1779f531b9a85d60d75aca26788ed5090085a8bb83ae421a1d975645e7925685f1253c88732f7e91ae1b7d8768c615fb2991f567321dcbf5be1bcfadf49209ac2bb9877d1e1c0945bdd4dbf4c09e8cb79b8fd7eeafdcb269665c90b7aa51c657007fedd48853bbc65facc1962af7d188241b671471afce9d292ad10395b456eff6aff4819c0a7958c148604392058fd3951e3379d687461e6d893c3b0356a3b56707ae2921815752563576814e7c158a9dabcad8941c70e12489646c5c7c85e5a8fa97f28c28f74fd91da340033694b1c1e19f333e44651cf1cafc290d0ae4f997b2794412bcdc4ddcbb69e559a8cca486ee31010621713f308dcf0ad02fa4c3cffcf7b198af2de9dff204464553e047a95929acbc73d54a0c8be96de6c2b4472f6898d9b1e1cbe9bb2cb07bfa8047cab036915eab62b1b90f3eb7927bd36a589822527604efe3b670e53def0a397c3e8abd1c62a1b5be5d602c1e8230c8716715cb92e522809b7bd72c5fbc29406ea2b729a5636640d84aed2d86c44bff6893598a0f11897b17c2b0b154b63561302f8cf8ab47206c97385a211e9e8023735129b6e752268e3a1271b278a626b20235d202f1c2446c162c8851a02ae3e4edda1ed7a0cb4800581b9e4a440dc8e6c5f9af58da7941cd9f3eed41c6ee8b5568daa3b0efa5e8b5b761c8411c683cb33fc15d8df76ea743ace32632da4c0c4b7d36778e078a3a6c116c04abc2970bd3dd4eeecd2d64efcc11782352528ad4ca7d07c2d5de722911c125cffe1d5a6163779c1fb79f17b0e5381ca2276dd3382b1ce652f36d73c4e2e4dd206d0d05932c29c26a4ade4d3b6eea746a92a831a1f41a5a26950e3bcafd7bff10cd4dc07694f4e232ff2ca560e78d25b6ea02140b4af0801177cc7f9e5451fd291813af2863357a369d4007ea052bc5177979c49c4b9fb9b5bdd58252f16b6c149d15e040f03fca685df50ee177c229efb94070a3c1fd36722dbf9bcdbf1c2b42001a0d9da446e85a7de3e007c26ce1bd012d884b4d910676dcb97bb198097453f9afb0d23a8337c6f4c3dbb3a254e166c93df3d7164d652068b692cc8230cc0b0cb28da945c7a75b67ed1f771905eca70ff2c8f241e1ae939472fdb5f753aee8eea4a9428aa2adeccf44fe62739c207bfa04a17459bc1de53a5f8ba40a8e0a53442748ea22b02526868f8eed3e238b0a2bbd10dfb13c0b88f8b767877be83a4ae668f9309ace3de2d11bc4cddd508c8135025b1a5692ecb39a8d88b84adb0ecce800b65ee5d0a9e8392ff96bbcb0a31c84ea6040b12e57b26fe3b24d15647d23f53efecd561d4c73425ce5fc305baeab419b02a8db692180b91be199248853b69f5e6401c05297165bdb6c02d171eef227851031cc3d2e76648e4553d67bf555eceece434d8a62c9a19d16d3f39abcaf043e68b4c4ab66e5ad809b8bc97cc77055313ca1da0d129efa80aa99d0a1c20467b9ff81f2a04b15ce76e3f59f53c4f53ee9a7b342965bbb7397a9f42648a46069bcc1d5c11a2bb0a10be3428ad45844accd70a859f08093860ff41c14410e98248ff37f60f43083f32cded8202a1c080ac4d2c39977a00cb3e6d9bf4835b87d7dca8c202ca132e137ddf3264a0a6723a4b0de9949970418c8836e2d3d6f6426ebfa44240285cd479f80cf6ca125ef7983e904701bed7c963737209d7e17663cdcd6f883e8489f523671fd40cba71d67f45eec27f712f600d32cf460fdbbd6376e09202e59a5ea9e8af8fe2c4772b2f6baeec235aa4afb51a2153c57f587b08415c21061093ed1ba6a2d84728c5a67271a01c79a914f1f1fdd813dd34eb3b274bd54e4d9a2e7c16c0643864a169788e0e9522ef763460560cbce34201abf778c8a0bb5b56b17a473ce59ce051c096ad5c248e0f7df4596209dc26da175cdfc1ace981b750f5fe730aefa00a894ef7b1705d841278e8d4eba0838c980a163f1cd198ad1b42d9de101fc2d8a3eec0ee9f6f5a9bb759fb249893a55f8cf21260cff055b3c7c7cc2813cb04206f9218936f6e204be1df6971b9d55682c79d623be41bb8733346e9eac1b64ce0535d9b18f71fc801f93c89e674de8b4731a95c18b3029864579f33c9eac4532ab3e8bbacae294c9d8308902d9bec095606fae9c7676908bdba2753f2ff84f9d9a7428dbc58f692f079b2ad870628b93c3af579478df1d7f9cbf9a803e7259259cb23cd8a8cad0b309581365bf1df055924c400655311b058c630307ef2a9ff2c210c75a61a4ea2e4e95e3aa3a9f893df7cbec137675eee38b477c2e72604ada65e13dbe224082720847ebbe5a41a1652337e9fb5fedf496bbae296ef8cb9b3ef7d5267e47ff4316073416350b219b359ad9047b5824faae42352ba6a5478486d68919a3bbbfd00fba64e9ba6f0fb99c4a92dcfc664d1fd234d38486ad2779ee20837d6567981524e6b2a93e7a6882185731354729ad82e45c6224467904cc31ad1e9ead8b658b88baf6b369b88e39a8ba4664e212031edbf3e0ca5045632c76b87034644bc5573580a1818f0d61d1e9f8eee76dd52d0a0ac6d1d60037cead13187c47cd70e690e3892d8a19171eaba1f237e7bc9abaab935e772989a4e40f2557df4cd330f3197c4ce657f9570af660b3c55a1224d000dda42ffe5149a86d00308cfdb7409c97785f064a96614cafe50f32056b06e1371efacedec3928634af7d5b9a327b368db9fcdf38a8397d72055371ea1c651f3c7c7735fe305ddae033f5df599136886134e98cc92b9777673a9d39d7a59dc27cd1714aeb1009f4209b373bc65de25812b72af5e5b4c4824a995d38d023b69cb97745af784b7dd746b0b69770f19d8467b010230823a5d0d9e7e17675e0a418404214689fe526d9a22db3f671bd1cdcf3ee8806c7903ef611c3760740962ece8663be6b028f9fe305badcc706b1432d8f8990f2fc26ce08393228abd4070d26a157329e968c6ac19ec260d55b56b439fac253421ff51a0f299581fefe529650f5830342eb4e1ab95490c4c359c8c2c52a6b7cc82d58d9ed5a44f290e568304df30cc5cc5da6fff37afcd22f73d4d3fecfcc343745e59064eda005b3cadf0add6728508b12cbb71b3aff83dcc0d348df1e0dcf9ac4ac661c675c794513804f459293a943964d71d6d2901d4ac5a9f6df859a2406213f27aa820e1035a1d89f83be0eff7243023cc20f7eb2d425b470c670a2f4e42c6a85816ac9460af887a5c694ccf0df4a91fcca7fed0df8f5558336e26727e39cf4894f915ce6402bc5a824b810b6a71313e6a7673a1e0309eaa6d426d3480da2cd9c29024c25fe1a3aad4e7a20b4652ac811bada090b387acd1c0e485a63966519f48acc644766157e5130b9eb7eea3c095925890bbd58a7220fb1c1a594bbd0ce9ffe643bbb948d226feb90b893cbf11b845634b358811805a1a5cc72a1b1df3d7b5cdca817e68f1d749a0c58b10939f458ef787eb5fc65f98ea4effaf86d8c5739365841ce0dd1f29485b3ba585b30f600168c5416fd1aafd6d07f67e4d5484c6c4c7f1ffba56ccaaa2385a2c8944a1f5cdd47afab02252ec0b0db4959fbd06c6548c7b5f2f97e3df8a9f667fef35f44ee2884a338bb990f001887d04d878e93de1912dc871bfb02c34296757ed8bf00ab253c8773e995a8288f2eb981235c2b13829009ed53555b55494e9031487dca79d0d84e614ada7a38e390229acbaf4cec421ef544e5b4d34a534af06a343fdca04a8a9849b13f2eda58f4df6cb517b09cfff0f8f0d4763d74ac4df620f98daf7d2ea34228af0e9ea39cfe937f27087b61faf50998a21f98230108bb856e0fb0686207b656c30ed881a0f9fca73370c3044ecbf790e7efaa5b5ca60c098a8f9d5f96f735b35eeda40ac5c93b5f80812f331018f477c747122cbfc0dfc020ac0385dfaff5d4274b220d640b1c2e287b08a35bf8205074c1834c056d30e45dccb07f1a46bc5c820bd26986438d4c778492bee1f5e310e0ccde8fe67db700c4a5aca27d5a7a999d61feb9c53142e8aa96a9de210d38c95df81e27303a1d0f84cacf73fdc9f145dd542d8b276e9a1dc7155933151d50a56cc4e06eff619c76fc0044c3895dbe236a7f5a3aa257c7a12455ff916867443de37adbb54d62a229527dee885e266012c279a804cea84d69fdd83c72b890b3b71ea663847c456f982a1095c0e7f88a78212ef90778d02e88013311356d8ec79aeb5a59282bfb817b6c6bcf2922441bb61373162c18aa91a5614dedcb427102147f67c0e2ec8cafcc4cf6e1f2e1fa485ef65dcf04ee652d64039ade6fea2aa5833acd1803067a8a9f352320e644a70273373a9dff9c16b7a05b8ee1f63d66dd19b9c7ae1d8bc0b889e70aafe947f5f9dc1d348d985be4420a3974c9680043052017aca2bf873f6a3873120c90fd32ba23041cb58a6b94f62b7693354449a4e0cd1cc91c08a282ebe906ae869dcd3694538e5b3cc06c48b3f53194539d526ed6ade4cdf7e30dd4fbc5d4eca47b03674de6159e05d6bdff26505fc9b4c2e0ce134d4860e2f7ff7577b6f40d8199c456370f7cd045790ac76b9196fb2e711012a2f097b1f82501411ddf7439e317a86dfaefa1d3b55378348d5810b14939aa5a8067a8409578867bc3b14f63dd30b9dae423d658cfdf470611559202220e4dfa38073e8e84b935d042ad2d882a352bba324f98758e549813b17f44737064f3e78cc8705593dfcbf553fc82eb1987ea83d24f1a2744b673808c87822f16cabd9282100d84fba0727e0078eb50566705640dc1f76e5fb2d2b7e68742a90c5bbd0a513771b034e050780e73982c0b1a4189d517dc2eb171c1b8a3f8a93e32268f8b6ee4be3138fb331044f3fee72789f38e1fa3a567a5464f058868e3f100b0e8f98b3769d0fd5bff7a9f90dd5dfc7c8cfd736705ce5c33e4b80852b9fb892a46fe5dd59456521ecd82c807b03889762d250afb0d0721939072f3c988f34547753116e6b6a4d4daa0eddffa23a0b157cc7042ed1ec785761c671945c0ed056f8c915cfd578d6122c3b409d45d8fc677976cea79a280630155d236c641efc07067e7266cdedfe756693887f2e9a8aa88c405c370aac4c3467406189e6897f4a6f300e5aec1743ed0350ccff209b40b7cc267a954d3d25b6128d6d62001c8fd3af77946a2ab36f2a9590d024c140d964623848c2ec34de6a08f3b46e1dfe89eea08146be1a316de8bc8751cc1a0fcb0989df2ec5fcfd80b5af057435a31e8eec60a39bb1bd4f69c2fbd62a40e13b474bf1cc86cdcbbd5b992c253b99f998a2bcd0e6dd4e1a63b05bf4962578680566b2422ad29194cc1638fee031e39ca87cf7c91337dcbdd2ba29ec6ebf9d2268f5be793ccfdd6bb4b29c47c52d3082437270de380ebb619fe0d74190e56f7e08bfa05ab3e695d9a97e6b318139f8c9a9af62e840c25187e957ce77cd68f84d86f2b4e469743484f01f1c1c6462ec5d25c41234aed3450985706e7f723162312220caf4a29cb82b2c6d02a8981f3037feb135f63083b377ccbd73114eba9e537d2ea6d0a437f900759b10b534ce56ee590e9fd83de0a4f834869bb33633f28aec1133f9d9b4fe188198164d956e2f796ad800b6cf2fbab06794799b260c0a1f45bfbd0290efb225452662d5a6e67a381b1ebafd7fb889af25c408de018ff5d0ed4bbbe8154c359a66aa3a360a5e7e7dfb3e7dd7881f19a42278a64bd508e84e09756abb399d9872788439a34350dbb25c1ba4ab8af0e6e46f3bd7e0c49f8cac8fc2cae89bafaba20119cd629b09290101abec57dd9bdee43f2ad5a1b38b9b8fc17c60c5ca199081d93bcf8dc3b38e077dbeb5eb0a8096089ad385fbfed077be12ce7a457f0933b8460ff1ddb3d688126f1d0aedce60b846b58b012f01149dbd271e651074535f870e7c876bc3ccf1e81a74ca9103ae535cfda12a8f18a9725916bb1ad14e95ec8ed8f6731e4e63a840daad8f9559535f9154d4b92591b74a18f1318f06f686642f8182e5fb471f29f7ac3bf4d0187a61a817e9eeb7280c075e4cf90b07c3cb3cd011c1c5ea99658e0d5257a12c31897d529e6d38f3ea43515bb43a458c2966516007db15087fc6b5b9024291de91f2c6c0c2225d6c2b498e9c2b65d0aeae3fdac3eb71b2c98d6f07fa7ad4402d9a0b8fcfab1510f2eefbeaa6fbfe6d3f8b5260ee654774ecc257f7c5ff708b6e41c6b5a535c1041a6256b469dfa363ebdcc14144af64b3437d1b70b6da56184a47f7c101cf687eecdc02c2ba1990d3f03cb2c9f36688d51f810d303318482dbd3466978b8c5a1fca14384207c304136f394467cc0f62d8ac943a65ae3f23460f840a1e16f3b0927da54c0b7cdebb0c2baa53ab90cc56ba9fe8b71a4d75101fc0bfff746bc40563de90ea1002d5a0a64a0d51990d04022e431572582c7bb95dec5bd0b412b58d2591f796cabacf89e2b958be17f2dfa684e354669a166291ee91b189979bb6ee14f17e0941de0aeafe9919928718fbb6cba40e9fecc5e85d48a6560df15cb246b305fe73f6e3219b873aab8e5f1e1126033ea782ed843097c8beb4c0bf63988e6f581d7f1edb0ae6b2fac7cfce55473359ccd95b672cfac2ce37e566eef4f0701f2745cccfcf19e032ad2725e9a37a9e9b57a6f8c719442c979b1ace08be0d0a0af7cbaee352d66add9321e8af181af89f1f0cd7b89c7236806e80f86c4ae37ee63ad45318787e41eff4324535777d82fd92c29e1fb07dd5f0fc24c611f28f1b45b4a402db270f86882f9eceebd96987e7c5407bcec10375e86b7720f337d4dd4a23351a3f5d4dfa3b0cb88e72cab1126373b5b0c91447f046871768f703b049a6e4877b7426280f75c437c433f33446c4406fe9d0be94703273110aeaa31735525b39be0483058fbd3650c8297646c14baea9c32ad2c6c0280230469399de5501acfc8acd4f86e7f714bf0415a9885abf7fb76abfc2569c0c8167bbc9017b4551f39d58cdce5d43c27c26e5a434aa61b8ab6824e36acfc5b3e152887b46756738dbba2a5c769a5b200f1aea547a774bf65288fb2f2e0e133401bd49c7a21ef4fd78354faf15cad202e93b21714e1d7625a71f0afb7572a88a8b7066be1833f32b69260cf17ef3dcc8ae57772d9f077b420d15867421fd4280bce474f43f841743763d3a350c8ed7b982e5e84a5ab42b88926801c6c34a9576b24ca7753b673660f6cf52b46b11e18128977b09fbed8ebfe8487cf263766cd11252283886908586afec28349e0b0df50fdd65eed7e68d829e4d80b6d9e5b2f1044bccb7fbd4bc12039e681c0b288d1692593c77391a8f3b22694e1812d884742bc586cdf8ed37b31437b2c40b28ff37113edfe8438b9e6b7c6ab13fc470e98997972c1c90c1dea2ed2177ec9d401f9bd19a3dad80c6bcc822fb53af63699649aa7956f6d2bb127eba051678f10c3b57c44069873ecff264dc196288a37b3f32bd288678a37ae8e55cf2ffd1d88d1518565f93b8f927c228bb85c7dd2b61fa02a4c87309fc6fecba667a5a2860f9f917176dbbcc234f95820bebd09db43437c041591e1111fccb37eea51d208e459cad54387adfcdd6c6a0ca20ff635e8af39597af4333a3e181ac891977abfdf99076ad306ae6b3e1be440b5a9b8144b9979054b67e8c9d39483ac4a9cebfd8c010052b2310bab588939f9c4243bcbd3c39a4cc86eccbfc3e9360e420e96ae418d0ff1e3bb48800fc9e3af85a0bc00cdb9e9a09bf858a7c023919a4439fc7000dee6f2e7f7237344f33df563d15844fe81020ca325357575a05cb1fafa54639ebf9e42fe0eb86ae375c4b24d04aea44a52575391a315e1025e5d30757a71e965a6a9318911354540d86e4f5fe2236fc24e8bdb6db04d90cfd956e1d175eac0c8d63a1a570d2d32d53917deb452c8c911249b8efcc3891d14681a681162b15684aa1c9edf83313011f76bb66c58261b547ba7ff14d81f5720ddaefd3027cdfc9952a7d29bfbbe04043ec7afbe891c3307008df4cfa581e446baf771d670df71f3d49ee0630fa3f99f7b5830a5b43420fa41a544971b4554b4c33851a761c947cebe63fe73c1dc3e0f911d179108e0631ba14ba66090f6dbf40207b1b8c26501488760dc28685d5685a6bf9ba6b767244920d2eb05dbd082905e5f7176560da36f86e3c35e1b5a83f2ce689eccc09d174c4be4fe22bc9344a123f1ea475d1253092d14237d350f5a35edec2dfb3b5a6c956a4858ce9f57aaf71cb0c11c82138b26c5cd2ee9c92b0a9871da2e26b609e8706fd3e0f11fe87471acce401b317c5e37f109311f2b38a8d5127979bc90fa75ddad27f931083ee0596fc94da7586cbe3f71017df79e96afb6583a9af471f785efa189486dbcd408a1469f31464da5bcb60a3b8b0865717002f043ad678e78587835fafa7c8a51910889d53e3190bc842235f785330c3b36b1fcfd2fdb6cd661901d00b33985c01f7c23c19ea4def8086ec7f7d56e48906b20d14a27c3a0ed35fa18add97a80d2fdc72514a03dbb1b193e31e0a1a5d0b782785fc42c7d7126b8ca029a0781ef2ced3f0f103016ccd98ad31f833844ada34959e09d9fb5757d1f38d2ef7b45f46f1336abba4a7618836954cb68b89cf11f819fcbc968ad14b85b1273d257ff6f48921fd6a86e98c9932b78b0e3b0a1ea754f8a5e3865a04fee8a29876eb11edf39eb8ec2ac7d0beef487cb3bd3950df6d61e7ce21af4f8b2d5303a646e76fcff7bc6f6a42daf2c1498ca66413eef8daba920aac935c9b2b8b9138bcbfbffeac52fa423ed2bc05b87bf636d8781fcedb16656e148dd04288d259ed94d415434a97f104d57a6ab9b24a29835be593cc99e23a2811dd1c772316e43a89deafc5d425e60954d1ebe7a13426bb0cbff401409b0f1648091170975969a235741d640b1773d9968136ec4ce905adb43069e5a10226d4070e7c20fe385a4a707508757cf90bf4f934a683102289028f9a194aa23d776042880d3d7c3336cfa3c6314ce1799e927b04284b1f5b46f4adbb2cb52c0b05b56fb7ad12b05fcef884b7b6a8c4972c8f82b35f52f6158928e648eec0226d5b4393adde553e2b05260fdf61de3ad7469c7910d92d77020bf37c9bec011d5a4b1afd589afa74e8157ef7f90a8287ff2784ce367d0060eaa60ef06afe8b38e2801d60aaa9e7aad363c3fc5bdf330e41d685b96725296b1a9add69172930da81256406d489351742414565a826e62be046615e80cde9695265027b67294432cf88dd86a8f89b59de830c5ce9e80cedfbdb981283a9f15c71a8b16691bb1c446999510a72c044772a1f383799ee2fc2aa6aafc126fa74b139f7aa0725e7684482dc727789fdcff14248c9ffb94a58b10e67773f9b1d4193656afb7614cd077cfe05759b8c720c74b9eaedff988d957fb10e241f14ed1d5fbe4df5b6a3d52f9f113835b2e649ab02094c16cebf58cf31e1be34db48bac8f4edf925d713458de6801133ffa4bb9d5a1cf1168c68f90c4b930302aac553baaed6623dfa4350f99715bf697cc4c5e8444c90efb97044030bccd4cdde92ba457944edd938e3a5fbd74f1291de19a139c242be4f84d79049c564571d27f0eb9760054fe6d298ea1384c7dcb8a202ff5398c3ff5527993458d4e4d17f450e2c92d755294b6727a4c39fe9868a48349de58bf899bd8be9ed6d315668f72a5d7f200b6c5fb265a90035e62bf8b7a83330fd87638f22c764b61b4aec0c71be052e1ff6cc20d3ecc78ddbf14ab357822a5ce906737422f48d1842d0d0c0e414e6bdaf8f997a30299aeb74013e426f865b3220bbb17e253b19a8a22db0c52771cbd602ee954df12b2d0bc62dcd76cc38e3d31d600675d6c7c87ffe106c763df17051fc29ae5a31052e4b7228a785a60e9302d89c0e1812888f4746c287c12049bc563dc56ed5009640f0436c793e8605578f491053d12b2a17d20e735623241ee3f4062759cfbd188c487b782ab27b73c459cbbe1a58d78e76dbf77ecd64dc758a78bf6b039f76cae959cf1c6c465a481dfc2af5c7134bb4de8090b3a77c6e255ac80bbf501c940f1a7cf8bff0a33c4bf2efdcbaaac616f0bc7139be958bd7a19b5039d6bc4e55cc0ca1bc41f3f1bf5a6822a351424e195507e403585fb26ab7c0ff0fe2572376266672ba33a1a325c8a8f6cd9da54a5aed2d1815dd7130d0a9495c936c43790282c67061421a772b4c57c8cfb956b10932d0d7a7b6a312a5cf9fed9d923e91e3275fd2a054158bb760273e0dde6b94cedd1feaa665cb426b64e5e739d90ecd875f215f3e8e1e328f59b96608b9191d4c1eb861edbac5d9d72ff9d4d2150ca9c32c7473ece5e15598aafcedcd199fa45388be9155a78997ac827a20787a0083a24e876ad34dc6e7f01198da7615cb418df16955a53a78d1182d04651b429d19b053eb89324a393f04be4583ebe33fb980b29dc31e4ad7ed4e0602a46aa5794d1e69b5d180f3a24cfcf2325d6c1e887ea773dfb1a2bf9819654495bca01d89bd617d60f898408f3ba7755693b02fdf52f0f47630392d23f313872b866bbcdbcdc796e2630418fa2f436fb60083de3bc773f3a3c0938ecd4215a7728e68f91b5cf5e167e28d7fa03eb174ffa78f7ed948e08ff589589e259f0b678224fd4d6ce6cbefaeb9f5acfe4e59004d2c2fdb3544474e9d5985b9c05e3f3795617e2bdb00bfa0809907b12fab90c02b0d9a9384dcd6a6bcec1682d13ed2a6591b9fb1727222dfe8272ecadc85bddb3bf3db1b0479353727f9c6afc3b21b1ad3efe06bd10f00d6b8d9ae87c0b5e5096eaf1b2a4a36a32beca1d4f625c5d3bb72e8d4b715c13aaac47397a39d4d9050d41e114bfb046d28d3c23ca73331a6c5590a867961090e515e8ce35a24e4bec20203497bfa1aabd1cec59df6aa8d32550fd48f11d2f7b4089a001b3f727e95c22b073f08754cd9584f8b35ea640cc27db96574826a0278f47efa908ac134e0c0302e510168b92b152f5ea41d7acce5d9486e1effc74c969b6e0afd8d51b040b27de1854a1ff2fe5904de4bdf13cdb94e9083ec76f8acd48a8cc622d58bd2d41d3edaf5a5c30ff74286386ccea72da853ff623f0023b8a9b407b5d66fbdc0cc62b86d590e5d116608181137ccf4754b15a290d25ff34811e8dce22bec1dccd4c73e7711136a36da5a2c5ebaee30faf4803073ccb90ecf5d80b046cc1097d63bc6b92c828a49da1ffede52b1cd0fa7f191f6022d69dfebdeff0d31ebc787fdc9a1ae68a11172901fa4ebd97c76d0b0c717761df4b01cd334f90bbb5ca060c5fba54681059d50ff8e3d18e4c7c896288a6de2be0dd275676f80e97ed5302ac71f67c404fd24aaeb83a9227c448cf1c70413476a16e3a59536605366e3b0f041638b7a08ca0627a65cb2c53706ce8613bbfe6f4d35281100d7e20426f74b3777bc55ae27532fd51e5b6de956264f94649b1538927bab9fba2d1ccf96b0995b66955c7a49bea74f4a76a6ac064d78269e23655d6a5c21952220094496399ae7f1a83efa89d037307fe40b5c78287d269ec323bbe4707c6fc1d93d6f71ead48d54b280f24b3175d1c650d5e43d9088b49a8f71f0f577731b52d27aba88c2a03c7aa66a599df3ea0c3ee4e2760f44677760749660344769b5791a68bbb19bd9edd2676417f366de614d25a7adac3acfe010bd90dd35bfc28bac73fba73f4264b36f07e9957b0b3dcab65ae887c60faaf9fe0548e2c8024301669ef28223be7a3a35616f7fd80811463d3c11795194e269cbcc2e09abd69fead2f8ada2a8275373a5aaa21dfa973fab8f102f0e2b331da55c49f74518b4649c72ddeacf30f97aa1a5d560514892e8ae8aa01410c2271f1497e0674d97b925b9c302183995f950680fa726f5430654cf4d6c8aa5f115aa89a6687399633c1e456da66331cbaa61541ef1fc21027078f40d342d6144e846e179e53da34f5f9316612a310b6887f68269084a0fb7c9d064f29ff39431c229e03b4267917c34c542a90da055aecce96daa7f4fb7397d01aaee07e317b05e1ba998ebd878c726a00c0adf466293fbf206c3fc93f22f65b6230cf371fd9101ab51a29366f6e433982aa1a4abc8d01bb587ba5075ff677258e94af8450c77c57f75a399867ba9da8ce8c46f7281985cb54cfc20a09224ab6f9c51eabac4b79d0d2630ff46f40f04c4f905ade1aea8151c6290a51482d3696b173eb59f4d56b0a73f0c156a2bd97f71810777c3d983d1d0f6ef9b7c1a5527661c7f901aa294698a1731143cd8d4474128d8c2cc10f864739613bb74c5ce9bd728d4f6a3dad4167beb78a6541be4878f886673dd78218ffaea86b53c87b783d925f5dcf66dd778672395e2ddbf438d2cc0d25f8fff831f701802e55d02d2cab85ab6a27c820e7286a1608a004ad3c8c5ec36ab2000000db0000000009427810ca315a24b33be3567c924053c70634524c93e0050000009b000000001c71575e80472babfca4d57cb19cd2ab57a48a151e29a951000000f800000000be2c6570e5b927dcf3c553b68220d40abcc73e89ec0ffd760000001500000000235c44e669d11d075560331b8e957bd8ea6f925956a818cc0000003600000000b29e17ec496b9a5d8d897bf5e121b8928ac2a094f0c5752b0000002600000000ffeb4e34aa1481942f5b6512856c85bec09203e6e02b03a30000002400000000dd5e3eaf7c69f9c1029d43438cd4e57be1053150b6a6aec5000000b2000000001d1d011f2b011f2c011f2d011f2e011f2f011f30011f31011f32011f33011f34011f35011f36011f37011f38011f39011f3a011f3b011f09011f1001201501221504285801311201321101330b01340a013e37043e38044235044236044a2e014a2f014a30014a31014b2e014b2f014b30014b3101563a03573502573602573702573802573a095f3a02603533603633603733603833603a09683a01693505693605693705693805693a09723505723605723705723805723a09763501763601763701763801763a08763b03492e7800492f780049307800493178001d18000000e00000000000000000000000001d1c06ffff200000000000000000000000011e18000000dfff20000000000000000000001e1c06ffff2000e0000000000000000000014c2f000000000000000000000001680000034d5606ffffffffffffffffffffff00000001005c01015b01025a01035901045801054001063f01073e01083d01093c010a10010b09010c3b010d3a010e39010f3801103701113601123501133401143301153201163101173001182f01192e011a2d011b2c011c2b011d1901202b01202c01202d01202e01202f01203001203101203201203301203401203501203601203701203801203a01203b012009012010012235042236042237042238043227013426013e57043f57014e1501770908771008005c5c01015b5b01025a5a01035959010458580105404001063f3f01073e3e01083d3d01093c3c010a1010010b0909010c3b3b010d3a3a010e3939010f3838011037370111363601123535011334340114333301153232011631310117303001182f2f01192e2e011a2d2d011b2c2c011c2b2b0121351b0121361b0121371b0121381b01215915012115170122351a0122361a0122371a0122381a0122151601233f0901233f10012340090123401001243f10012440100224521004253f09012540090225520904265808012609140126101401275807012709130127101301293e10012a3e10012b4210012c4209012d4110012e4109012f2909012f2910012f3c09012f3c10012f0309012f031001302809013028100130020901300210013227100134260901353a4401353a4801353a4c01353a5001353b4401353b4701353b4a01353b5101363a4201363a4601363a4a01363a4e01363b4201363b4901363b4c01363b4f013739140138391301393714013a3553013a3653013a3853013a3914013b3552013b3652013b3743013b3852013b3913013c3540013c3640013c4057013d2935013d2936013d2957013d353e013d3517013d363e013d3603013d373e013d3717013d383e013d3817013e2835013e2836013e2857013e3516013e3602013e3716013e3816013f384301403544014036440140374401403844014129370141353c014135170141363c014136170141373c01413753014137080141383c0141385301413808014228370142351601423616014237520142370701423852014238070143321401443213014532060146320501473208014832070149292b0149292d01492b3d01492b0301492b0801492c3d01492c0801492c1401492d3d01492d1701492e3d01492e5301492f3d01492f530149303d014930530149313d014931530149343d0149343e01493403014934080149340f014a282b014a282d014a2b02014a2b07014a2c07014a2c13014a2d16014a2e52014a2f52014a3052014a3152014a3402014a3407014a340e014c2e02014c2e07014c2f02014c3013014c3113014d0207014e1515014f3a5101503a5001513a4f01513b5101523a4e01523b5001532a3a01533b4f0154283a0154351a0154361a0154371a0154381a01543a4101543b4e0155354001553640015537400155384001553b410156354801563648015637480156384801572a3b01583a4d01593a4c015a3a4b015a3b4d015b3a4a015b3b4c015c2a3a015c3b4b015d283a015d3a41015d3b4a015e3543015e3643015e3743015e3843015e3a53015e3b41015e3b55015f2a35105f2a36105f2a37105f2a38105f353d045f3541085f3542025f3545015f363d045f3641085f3642025f3645015f373d045f3741085f3742025f3745015f383d045f3841085f3842025f3845015f3b5301602a3b01613a4901623a4801633a4701633b4901643a4601643b4801652a3a01653b470166283a01663a4101663b460167293b016735450167364501673745016738450168354401683644016837440168384401692a3b016a3a45016b3a44016c3a43016c3b45016d3a42016d3b44016e2a3a016e3b43016f283a016f3a41016f3b420170283b0170354201703642017037420170384201703a5201703b540171350301713603017137030171380301713b5201722a3b01733a41017314580174354101743641017437410174384101743b41017413580175293b017535520175355301753652017536530175375201753753017538520175385301753a540175415801761558227709420177104201353a450100353a490100353a4d0100353a510100353b450100353b480100353b4b0100353b4e0100363a430100363a470100363a4b0100363a4f0100363b430100363b460100363b4d0100363b500100223559000100002236590001000022375900010000223859000100004c2e03000100004c2e08000100004c2f03000100004c3014000100004c3114000100004d0208000100004d0307000100007542580001000077093e0001000077103e000100001e181806ffffffffe4000000000000000000011e181c000000000038000000000000000000001e1c1c06ffffffffe4000000000000000000014c2e4006fffffffffffffffffffffe1ffffffd4c2f4006fffffffffffffffffffffe1ffffffd4d303e06ffffffffffffff87ffffff000000014d303f06ffffffffffffff0ffffffe000000014d304006fffffffffffffe1ffffffc000000014d304206ffffffffffffffffff87ffffff00014d313e06ffffffffffffff87ffffff000000014d313f06ffffffffffffff0ffffffe000000014d314006fffffffffffffe1ffffffc000000014d314206ffffffffffffffffff87ffffff00014d310e000000000000000000000001000000004d310f000000000000000000010000000000004d030800000000000000000000000100000000553a5300070000000000000000000000000000553a0306f90000000000000000000000000001553b5500070000000000000000000000000000553b0806f90000000000000000000000000001563b5300070000000000000000000000000000563b0306f90000000000000000000000000001673a5200070000000000000000000000000000673a0206f90000000000000000000000000001673b5400070000000000000000000000000000673b0706f90000000000000000000000000001683b5200070000000000000000000000000000683b0206f90000000000000000000000000001743a5400070000000000000000000000000000743a0706f900000000000000000000000000011f2b15011f2c15011f2d15011f2e15011f2f15011f3015011f3115011f3215011f3315011f3415011f3515011f3615011f3715011f3815011f3915011f3a15011f3b15011f0915011f101501213559012135170121365901213617012137590121371701213859012138170121151b012235160122361601223716012238160122151a012410110125090a01265814012608090126081001275813012707090127071001283e09012b1012012c090b012d1011012e090a012f090b012f10120130090a0130101101311012013210110133090b0134090a01353a1401353b1401363a1301363b13013a3514013a3614013a3814013a3953013b3513013b3613013b3713013b3813013b3952013d351b013d361b013d371b013d381b013e3548013e3648013e3748013e38480140293701403508014036080140370801403808014135530141365301413703014138030142355201423652014237020142380201492b1401492c0301492d1401492e1401492f14014930140149311401493414014a2b13014a2c02014a2d13014a2e13014a2f13014a3013014a3113014a3413014b2e3c014b2f3c014b303c014b313c014c2e13014c2f07014c2f13014c3056014c315601225915000100002f3d09000100002f3d1000010000303c0900010000303c10000100003d353f000100003d363f000100003d373f000100003d383f000100003e353e000100003e363e000100003e373e000100003e383e0001000041353d0001000041363d0001000041373d0001000041383d0001000042353c0001000042363c0001000042373c0001000042383c00010000492b3c00010000492c3c00010000492d3c00010000492e3c00010000492f3c0001000049303c0001000049313c0001000049343c0001000049343f000100004a2b3d000100004a2c3d000100004a2d3d000100004a2e3d000100004a2f3d000100004a303d000100004a313d000100004a343d000100004a343e000100004c2e3e780000014c2e3ff00000024c2e14000100004c2f3e780000014c2f3ff00000024c2f08000100004c2f14000100004d3041780000014d314178000001");
        assembly ("memory-safe") {
            return(add(code, 32), mload(code))
        }
    }
}
