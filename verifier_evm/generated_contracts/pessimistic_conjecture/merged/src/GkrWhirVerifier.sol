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
        bytes memory code = bytes.concat(type(GkrWhirVerifierCode).runtimeCode, hex"00d65401c88977ab27879da5e60cd02fc67f1c7795db7fa25afb7be3ae5b51f82ebd4d4627e81eca29bfbe1f00468c5da8b84c60a5fd50badfc5ca2a75a2386ef643e63aaf0f8c389c86c0e22511926713dcef7f7c31dd59273b3904c9c2ab1fa2a515c247cb8e287665e842b27aee492e41ca84e6950f57567aa6622a88cd7fdcdb2447050b4ff6ee563d745a259ae352c5b95f6b6884d92d0deac1a8a865fc6d3f3565a9518ea1683054363d341d9691cb2aac3f4e81ba32d0e14a44a71ec5886199dd2fd76c32c75ab0f2559ba51e28d999ad2055b19462152cae5a00aa882dda578692af73871ab4e3904cc5a7f1f8d09e03005356142e618096d26eee97462755ba7a9421f1f76afc849feccf11f283ffe7e9c701e7f8148824ec8456fc6ec254ccb10f09087ac488e5c5286af7d3efbadf003eb97982b5135d572c413e0af504163423a3378ac0482c5ae6166399db6e35346bc8b7e4e9dd87ce5e0dd7413bc7e2302ab90fa067fc23744048d4430da3155b71bfe808e3cdd8a35195a7499934307fb1379f4d4cfac06dad1e5b7b0b22946b7ec5e30eeb5330207ca97a2ed1a3621f102e205062f5c13fb5c95f1b4bbade253b7822b4dc823f4e3039b1660011dbde04ad9bd648bd1a7d776e61bf6057ee8e66f2feb69233822cf91d7abaf20d978a8084030d4b94b4d92f68786bc6d22268ecb114e3ae0b08ba35a4f263b473da68872796f2936a1a59468bb474e8132c9b305ba5bf24b212c7f90fb6c86f4478261e007fdfa1b03427d9b1f7bc0c10fa5fbf5e7981985d9de4745acfb183372c5e2776897bc50544752419f781335b7c39ce9a1c846f9d367e22f26f97166b92c87445928598c26ae59ef0524ad5cf29b410838f5e00f0b8e14ed680d8b683ebba4f3fe85876c3901ae7b406df5b8a36cef70370787dbb1dcbaccf9f68460cfe8380591a246f81a75750ba984ab3c293ff35a74a938cb42fab02b0dfba20991dce4b831917b50a2ffd49a4dc432592b44a1e3a07eb0b50b0fa6a5ceb78a37ac32eeb63effdbad461be62306c05a71f8079db5f2015bb1e298d887cd1277d67c0b61598172bac545c4b968b794f7657be615c83d88a2170349aacd1070f5c8832a5b3ac087b7bf194444383149c1e9789de231ca7c9777d4db2b255e258a8b70157652cf04c7d21eb45f6c21992921ae53c7dac4af13af45ca214ef978498cf6f31484587d2f2cfa7b14db68487288853b8b7e7c60317d4e297d01abf9ebdeca2e0f18966c81bfc0c543a938a5b3dee012d88222e8aae1bd97a86d3d244b3de7255ddeeb20fd09b3441f857d85fd7a3f437ffc7d32d93116cc173f679902c6040f25ebde29df69d18afb2521edddb251e56f92a223fd5ef3aa804a31ef609ff476f11e0112d140d0827264b1615eaea3a0e0acbabf99a81f91008ecd5a67519b9d305f209f484b8956548d56d0ecc1a0de50c83b7ec85b3cc0b0a868fd42495b057ba98a93574bd6fca8fd0a967f7b920dfa94f32739893afce4e465eee1ccb8bb77960a6d0179965256bf5250f299a256bedd3ba8b303e70550418124748a073bfbd55d1d3927f71c51d471eb8cdf5c88f61ee7b66f1a928a2605daa2ac055ce8aec53cdd7a1e665c416f971aace8e0787fa407f5f2ae23c3f62b705ca3be84f14d65b680c45d226e6be0c05a17477dcb5ec4e6d850a67a99055ed922b8e88901ed4db4f087c7569728eb8c4424c6f7359c2cff1c7cd8053c9f5b333ba0c293e7ca6ed3ec2138a1b3b99bdbdf75016fcc3506869adeb5c6efe5d5b8fa4172289c5999ef705a5332e85ffa720af0a015117bd78b8f13facd941f714f3e4413fae5ed5759ee48a1aa3e91ec7acfaf8c9e4aa3832e2fec43f96aff40f1d4cb467d902ce0d4e3a356f53aed5e873aa9f17cadefc5a988636935c8c98282e43b7e82a69c70c8661714f188cfb23cc0d93a0aa1c5285e47193d72486020c9046c6da9fccd3beb4e25e17155538d2629667a1af2c334aeac28909641f9b3cc3639ab186dac993a54a1dcc9f4bb38488bdcb682cee41a01340bd764d60bddd0b022e948f68b47d470da7a5ef8f06f777ec57fd88ccbe9a40a52ccf540f4db66391ad0d8fb0dc918b729883128506cf043625ec5e3ea2f527ad9baf118dae97e2214656ff4bb91eca486f201fb93c5b50c5f4f34bf8f30efa836a40a3b5e8c7b6982ca55111068b1bae8af43930a41bb92e46fde52b61ca762153819d5f89fe7e4f42e88ebe1926a33473937e61de54088c3ef0274cb4572a77f70b612a18ee1a14db17d077c3c15648cfb85687d7a0e8952219656b5f2da95dd8320d4536abd394ca3932d740d16825137b95d6676ff338ac4d8415697f2893f60ceb4e936957526d6bda97380b53ca19a1374d6914fb6de9186b8d3dc2209a98b95c28b1c9855b4c60e6e4bfe2c698a071b599e6787d7c0c3c58bd9dea41c3a5e0a813745dc8b31a52c3681bc46a35f9578c9888a96f58df6a7b1de28af0dfe715f33f3d6b17e81a1b21d497196935ab81984ee9a123d534187c7b8fbaa22c2a1771196c60142e3e9d1dc09399b783cdd8369b0f5ad90962d23f567508a37fc9737fbc22135147fac7601b9679e2f36b078ad661b70ad803dd17821c45d780d3c76b5159feb70157d945b553bb706853bd913533f3a5eccb79b787b777b7eda20f0f999170ddd667cf20c5c719aa9e01bf6afaa8d2f0a31dd9b8fb01d32bdd2bb84c7350b51502e788067953f3174ab87d55e30f6a3ca76d6e9763789bb0a2027a8d4980233a5730351d7a452963d3d3b834c3bb361b836d2aa8dd1d961c9d24d51e0ad641cf13fb9301809c23208429c5b4ee9a4cd65896306ae4b9b155a6fdeea58009830b915a0239f850e49601c8ea6051d0687fbf1398a8c4f43b9b4814b09a281fcb5b0f7a66f1ee082dbe531a33f04f79a776e20004ff24c8a4cfe92bf5af1918096de9ce772013772ced2107ba6de9b3fc3647b3290d2e906ac73af98660a10adca4561477722750ea456c1ba9a9a9c859f083cc7efe8df5d53fcfc829819d85312c5d4053a8cd4a736329c0382709b572a1d9244c35f86173f6afd22d119a5587edb17232f8fd68b6ef60c9662580f0f8bca5413d52327a901a7eb49b6103c3dd80c6856fe4d5175c1618cab046fdece0080e70bc70f2ba95331c40e68c87e581166aadf56e1dc5a27bf222ab5e704f74f5a1c0bc8fbd09cc7a1903883f6a047661dd6ad0344b1da666b9346897c7fe5a69c7f11656bd85dd4f488cf1b581f05537c7f90f93c638e8d6c1190739dea99b7c5319c50aabf8b6fd14142c3be3b0da22d5858a27311c67231e906b106d2f64c4ee5b75f88e84e18b86a23e6a24adc88f522905855e0081b9a8fe5fe88b5184e43aafb2e3e8d645549e3b9fc8a2f1544f00c0d485f1cb806b3765f30f43758bd8962d5e10f8ce48dd7d93ee8818b638b714fa602b8d5c0e264f222ac0ce8f53de6b7f5ae2e16a9827ac4fb8f0a67c052cb2b9579e8ad15f20c5374c210fccb530d204498ae5bc0d38ccd674d1af15c7f59c8482d2800434ef1867ea9fef3121520f0220d15c59d7bf0581f3935ae9040ed5322fde1cd3f33355a6537b741f6616d7fa3eeb177606514404d84dfe4707eb2501d1ff4064e11a6e8cfa5ed10bb7eb9644fdc687ab31366ad54de56be198ad48c14227e89a7f8cdeb5e0e785a33c269cd521e6b4a8666789fb60d7c3a021cf0e6bb50c3393bccdb1f3871d4f8c6346006cac88b1aecae4000ded3ce0192f9b610afd1962d1521044441c1a450d1e9cb0227e0663e040f78d90b673059df8e17e168adb78d08a7af6c973eb4e6f5e2916f7b7626faa7e4b7660e6456fd8f7a3d159ddf67f5e3f9bac7d6be9f024f67ab82c9ef4fcc5c728b041e4af9988c495b65fd21ba056075a8aab6f2d241432f9263549d80dd590298d2d5afecc3303ac980b2568547ab197803606efde9140c14c515ad436b330cae3947eb1fa62ee83b9bb52079a39c276b3ee5c56d4aa917f4a9c396d4f2730d9ef9c67a0b6d3c1c659fde63738c9804e99f3ff13a99643c6b663494198c583f55c73a2a2cb1154e6636d0ec13fe77f7dc7aa7fd73dbc78e8c06bea98732771e8bd497949d727f92b54010fb50094c0a989f43ba0ea3eebf7d9c06a034803ec7a9ba07d4acc0273260e324d52bb7a3b5ce26a6cc706eecf048ed17a3114eb89abcc7597a4e544c3ee10ae4fe4bffc4c27bebc18f6e454a95ba2bbbb5702906cbce8b0e8f41e7c868ba3518481116d96a807b7a8cae8cfc00a7101d6d03b57310fa2a98737ffa75105ec6c5c7510adf7f7064d7f36f9383f2aa09eb7c2987a60532f323221e982b7e6d706c78abbec9c5e17249c818c567669a696e515ede154eba9a7718ae940c405dbdea1f95599ce52ed3b0f6a71b9e4f06ccc49159cfee2b2a6db7e52d6761daa9065166c99523077bc77a0a748f4629a01ef845866f2ce1cc7a20c4fd93f96f9937aaea21cd58e285e459bea47143007051dcd1d4b56fe951b9312a95c16e938b3b0f101852d16b7110fb29afaf9c790b53e4cce6a693eed8b930f81a06b2a1e0b86fd3de3a723e32a2d035f5624f956edb2b7537b78718572c38b2d518a387198ae855d77993012a8f37740aee7d2dd658c1e35079e008424f654418ad3b514646c8d55f5de22cf1ff7dbef4db876e34edfd173a5af08be62e8825bc8e5cdcc2f261db00842bb466f4e0c0019d7a0df6db3fa40262ba9a68733ff60c3804d1418d7123597646fb5b256fe0065149a2ef9eb97711643eaf52524674898d43079586cb1961e2d6e53bebe590c67791d66562556d2503091999006945b97e6c593ad9169fa4a964d2c31e9ac5c9979dfa6d65024458e3484c4071b6f71972c5a53d3498d7015b9845f5bdacd50f531d6bc7de5e98deff25adc74f46a13640fd35256cb34bc677ee36400f65affd2a95dac2c3dd2b605c3e77d6ab1732d2989c82e94d038beeea5769a5ebd9e8269a3c788f5f98234687f213e5f49521ec7069961156d7b867adc32d60aaa1417724bee7dd7c278ece1a24a9ec609e2e404f08abaf9b139062e7615c1aaeb247159371bb1f72b53a7a415425332e68abe74faac87833cd6eb98f022a21246ee63a71320f67fadab3f8960aa3e60e99361b46a63a33af635d2d7327451046af358be2f7f08f91009b8a5015f1f72e3cc093ebf6f1ec36d15d5cb4f0a6f3cc630e92c5096cc2c9f1909b514d9866ed4f034040db03a7a67b82ee1dd168b45d68a8b85802003d9bf41469bb7819d6694d8d27384c5c6ec0874a82700f2f6e6b392081d6001032ac49b3b617a06adfbb712df4d0e357ceadb6e5f37911829a33672cc4d7695b59f85b12f0252c3e6d7d56bef113d1c56d441ae23a4f8a642368da34f4743ba2759108ff64599dccf9704a3a7689b458259d517c52d4e6c1b72d73d3b7090319b8d3107b5ca5baf2437d3623e4065cd56ab8f714229ead34a23f1ff98e38583980f77b1f39efc52ace59156ef2374e1022b12c4a2f6cd8535db85fb97247bdafaec0501c6fd15bb7d2c635e1864399c6a6b0505f9f60b30f683c8f5227f454b7d414842fbcc6ce023f80e25965539b3ad6d91320d322c5ebbb8279f97886a0243faf45b21128fea85febf583bacc79ab251a290c670fe23b093bb62b5916d22d2284c601348b9ec8aca813ce85c92da3c530da722dee6c96fad8ad630f51438a49e3bbeae6569e792037939cd96dc8526df8f3ebd12d83441d95e17c13ae5ce96ca2e98a73ac4a359a4ea627414f5efecfaae0671a23c3d1b82d9a1c83a11b5f45e75dca25a743c90aeea1e4afa7d4fee370ef525b183243c81bd58ff1bae0a689a4e760d0a27a75f8051fa4fc94660d0d6e87d9df3b4ac87609437b941d82c220778c8062f600789fa498a8caca7183498009c2813db8bb0689e34f032aa1196ee70f27d480e9311b48a0891afa9252df14865a80db993e50d9f354190c5cb6899d6b494791d87e5497e34fd2fff7ee052c54c4160d07226a963b2ebaa989f3d3833834597464fe36f17cdbea069e873353b82fc5405e27dc2e8323fec3460e5e885bb12597c1aeccdfd3ecc996da141b07526c1fa94b9d572443c93facf2fbfc0dcddce6a5be24858ebea56440548031bfd633ab94b31a150be963db5606838ce47d2f15159b3e356a31eb698b960ee1470d7d2556c18fcefe5478c6d9890484d38e657dfc9a1a2a1c0fb32a2cc742448c66246ba9add920bb4ec07017fd3cc18aebbbc4f9fb5c45fe694e0ce46e14aeb345cf07cd6c3ef9b26cb72eefb752d23600e7fbfac4db67a51dcc2e8073f6b4295c4549d6eec18831a423fd0501a7beece53492e2b8f13787088df9cb14760128a279f97ebafd39632e76525130e7fe61a4560b1ae922dd2a255fd6f14f9bd3366104795fa4a87812819b78362010109a5ecc8bd7b70316917301140174183ae1f1c8fce9307d432686c9fc04e14cc9811d60fa09b950e36450d537ea7c2cc0ac7a1cc41f2705d91722a96ad16d0b2949a224899c552743ad08eade59239cde07379ebc79c79c8f92e8d556e0bc84cc055f68c5df73dccd011f9712b59b24a0ed9488d853e0e970178d5d929c63aa458d89326ad6a28e92aa0eeb52bee8d0cbba9d1614dd341bde48e249002e10446936e00000661f033035df7efe3239211779bb5947fddbf3a4bf830bf778068e245379fdcde96ff1a31472271639a6745c7c66e3070509b88152aa377ea1b4a3271a0f167db267ba473adbaebfbe3342606ab10b600473f410b61705c07bb17524d4670a15871db45e2e7a524b2f99cf98d68e24b264affd802f2b328977ecb21b4243e84cf5cfe1ed05b7d2c5983a9a0f458f3e032f275b12fbc67d49746f0288849b029e89d65f0ab6b4cefabafb891ea633102ff3b22198cf95f235c75c11c510a059db9d1f9b3592c5afdb071a9e4e38b3a91999c75e5114dba29fa6ace6c20376c42bfbeb81e7acc63def996b2200a7b3d9b61b08fee6824c413b970c66dcb2cce1eac12487d191034b011a9458c490d4d4b9261da6d85c2abd41beffc80fa69c219ab73168f5d156eb1934c51f588ef535e05b664f23fd48fdf10b8fe1a210bffc7d528d833c7132ea60238e8825800aaee4e4e36e65eb1d2f9bfa99942837b6e79d82ca2ac835d15fd9f8e8a8cae458ad962716ce074a752b4bcecc36e79633c955aa3426954b8e14a42570f9325d56d382b949b37410fc5bfdd697385aaf53941fe29c2c99d615a6076064c114a3c51f8773d43957708987936b3234c9b78c6638cd3c6b71acbd0d8703d31494ba38fe000203284562d25c8454e7bbbbb7364d03c10adef0b00fb50c097ac88455a034da4d34001a4f4fcb290dea7625640dc8f0d051f385802bc68728157e2a11986752c2e2f62adfad53d18db463ea32aeb49f3af034b43ff5ad3afd3d2213b089697b154fb1c8e25762950d22238bc721c0b6530628fd854f214936f75443f493890ce0b5a3a81e40aa454b92b09661e82e08d36b0de969e69984560fb3080e1dc6f599345012ec17012d205eabfc57c09ebee3d58de26ff0a7ee8f726a14887dacffd2b7279f94914e1e677621cfbece8381a8987e80e4335a14ae6fe1a0949fb9e8eef72e8fdbc5371e91a9eb7918dc84cc39edf3f1d502207cb8dd41b318340b6217c1ab118953337a43b62ad97e7b6878da8ea9f9c90d9a0b1a7c79bea2790fb1d8047b208e028dabd660e0b5f8f1df96292de4d77f8728b8af0c835596b76a4e5ac7f6a9cd383979e06c35b4ab1059e4a97de288a9951e7a59ac17245ad6629044d8b1a809bac01356d44d2e2f481429bf33032d2d426e42c407c7a36746d0f587c1a3acbcc0b250e349f9d5fcfca5c0f945d743aa89e075fa278ef350a8406417c9391d938fd40d6e958dcd9191e1b171eb46c707cc97b73fe27f6a038c049118bda905d581ee5f6de5efb72a848ec1a2e4963b787c908aa5788cfaaa29da2fcdaa99b70b074570723bbe792221026a097af5979778d868ef822e0554d4c74a759700cec5aa489d4e3333e79be3d81d0a9efc821a436ac85f4aabfb30ecfb4bd279da5dbf2900fa5c0d816a584775aafae87bb573b779741019b14acc4fee92de3643b6ea964ccfda9c908a1f6cad1f70a8f570b5d63b6f6b8e9988eb5c12803bb5ff2775092c028ed1e9fd0cfcd159338aec3fc687d8d3663f971b24dd527c1660bf20904c2b496382e80a8ac518b9319bd725bcad5d4aa97f0a279c2565bd96f76452832d914cf7c1ca9b2fc53d6e4f98eb8db919b17b3ab352949834e6300b9537a61cc26b63a2870c4a197b5f93b9e629b6af7f7ce4893b865bd2d4104bbb28863d1af61c51aa3e9e305eec30bb2f73719fe33de6a9bb7688562f4854dee07c2e0906244271bd14fff68fff112df18422ba577c0a0f96008238cc81e5530d26d22eefaf2e221a68632b2b88de5e833592a372eb0eae58b4e250cd2158b15b910549e7094ba05eb06cc672ba743dc68c112019df17e8b0dc38451e2c3f25c855723e946119aaedd469918a5137c15fae717ead4cef3c667f666ae24ef6b630013c502c9f35b5625bb77cf6e2e27a8b2bda194a2eacb404ecbcd97c16a922d6fbc09c99323fb148b418939b2286eab82a132275f09b0a9960985c73a582a7f61514d583d1e924b9663c0ce0547f2bf9971c4160ebe27dfc4150f9773416642a44700252c69b65c2c2d8c536d68bcae3c13f05c5868cf19dbae01b2e03496c7b30ef505265e8c108a46f9b3bf5dc34418e0f077282799cb7fc29ac95de1cb4a20740a50a5040f286f1f617aaff18790fae9a1f4b60162c34042590364ea30f266b61114e5dfcb8c88079d9885ec5cedfc7e88598820fe29b84f9ad082fbd8e75e4cd165e75e9e14a5bce0e5fb53b6e11120f1b95c59b6d19e2bac47693ac9d887eaeca1bb1d7a49a1984694b20016908481c49b5cc904cc4fbc65dfc96b3ce0cb74f2fc7ab2d29c99b9f1b42f162d9b26cfff8b152156e90d54c2a380f905111548444439e3dc2fc345cd270d5faf155483178b61427260af9a1f72860fab5f923c21ba0717291856fb986070582061d93b97af407dc1972b2d71884fe9de4fd5c6933d413ea77aa2cf0bf5099db9c3c56e2230fec93968f220bda953526768ac2b2d80e7a4536f79ddb99e8a67dd003db22a3b4a2e5d8f2b3d4df61177b04ab5a9b0a3efc47e2a54bf6dec1f4f66632a304705b32b0f6b899f1f0e06da65ca58b3f4b84be242dcc71d7c9f54ac840881de5ea0c5867402d95f201f5abdf293f3169bd704ab5ee5c99798cf16ea79102d634f8c6160be0b6aaf722ed23906f28354ad17a52192340355085318b7c89d2741798084477cdfde841ed826cd736f5d154b96d8a2f59d73d8ffaa0a67ecdf1b8d07dfa3678c0c9c960bdce8e283ca250028b5afb0c9470b29049d32fa91f278253671c13459beeabaafe8072ec4a387c756610fc78bd3428715475c9394c805608d9c978fefcb06a8e70391af19903b9c98ff6f825926bc38c929e5629175a917826b9b2217b2ad950c21ecf126d23a618a22fdb9a7d92045251bf119858eaece7e426121960d4c0e74dc10c6375484f131bd60d6da5e56e442b9a512df3112accebb23518bee195c4b25aa602b77feaca2d8766f64b0c74bfb6e33d36f7b20acfbe489df93762e75e57496c712845a14beda54cf5cf00d8f10c3ac53a4c2d970fae40c882a9f26c6ba896fb16e7191ba82a7a290d99c6f2076723331d9e7c362ff105f0677a4f3ca11abaf6d82c1c6afeb6e7b2ccd729ce6bcfaaff27fdbc9d7a729cc403e06ce81866bc5bc60f7a1090ab01427e1b6758ab09d0a58da7485a1656e48384daaa36d5ce2359b95aeb27fd3578be023aeb98aa39b16ebc1050d7a91b35a4e631efe689b5bd8ba80c6d9bd932dc98fce0f3f3b9f96b8b2659983a479a8755107c9f01cdbb2677b7fbdd38aa175c429d97f36e3b5f640594e8bec7a989edac5aa69f3dc1a2de17f02263070d942aca2bd9d3ea789c79587a489d8e751192ff1e49eb3c134f9f2238ff8fe70e5fc12a9058878238cfba301a9b30202a4a3bfd4234924729aa99ccf7906285c4ba1e69eb134df551de13a9c092d24c255885d55e30d20eafcca1bf863a19d505dbbab06f74eaf4091ddf8bd71ae331cdaedaf16fc76ff5bceb80b3258a5754a68bbdd042a5c2c5995945dd972611acb585e2116a14acfa36883c4c66a5c14df7fa2ae9d48791fa30a57e0a936bc90990f06a0d1a8ca2dc3c5003adb64cc629d9eeb940403002c310c1ad0e76d932ff616b73e8a64b70adc1430a09f1035c923b207eeb58a760223f2977cccf59a0137fce5744410d7e9574abd7d13e563513f0863be48d9628aa6e2e5fc00f6d788728c8aba6915bab0d8481aec3a7025f01310fb3e0c2c59961761ddec371b9830687597e010171af4715f07e35296ffbef2914f0fe8aa51fc5a631fff9629d0c7b5f9bc2645206e7cd02c74472fbad9408fdffb2be05ba97cb2277879cb244807281fbc5e743cb39106decbde3c6d01f7d4016064bfa88606967e41908a0e782c3311a5a0faa7e8703a3a6937fa88972b0046db373325fe396e6dbbe64edbe96424f26b1a1f21b22a942f9e1ab6b88bb76ece672988ec3b8c4796e7fd98d97e1bea258a79822023b9227e375cffc8cbd06937556c8c78a46c7167757856ee8635e56dd6663cf301372011782bf59537613456d600a04af0009ce74097734de8c50ab870e6e3d6fbe51817b2c6f11f8a31ec8e952a258cc28548d11114db5397169db443e586bcb42170ee595336a129ebb3fe353a870b023df1c8a21b21963aed092d784d39c19ad2ee2d498b23b89403a871976de86e033187502919e817d36ff0d3a69b757354ab08dd84205a8d6ca7685069066d4b2394706c383a0f09dab2b3a4a6680102fd5d30951a114887c94201b01ac540f1e793d8846d4597186ff8b1701a6368676e6c929d639f1f7ff73bc2c22314d975110ed9fcc2849b5f4f765bb043b279da711367fa71911c6d02646d27058d23be659f49ec81e40ef6ba1f8eb25afb481e8e8caa949ab365ee8f3cbaf8806a58b4343a51cd70688cf44e13fe0486ca7c455d9514d8db3b245eb22118fa12c7ec759b696d9d808777e15046ec46d2b9c30c44a7764c846db412e662c6d31623d6853e43acb214fd6f5906f329bba4b2722ab6e4c90e0cfdab1aef0bde216317d1c22a6f8f9377dcf4f01ccdd36d51c08d4ab5f1a319ed36304726520f8e2a06d879c733a84eca442a45c5f9ddc62b118241889a2d4a707d24549eb2ec17c36f8d1c9252f3549abfc86c8915700ea4085077ffcce0e2ce217e22a60b76923f59c224660402ae88d8a0f53bc8b2051539e809c612ea8ffe5646a7c02ea1c3220a53958baa8c14d77428c59d32cab168c9bde91c835177a7bad758e0c13e44e3e1404b897556b049e33b3736972ba46a6806ab5d8b66ff26fbbc862ee07adc3b169dccb4390651eb91344f82e88483ebd0bcfc64892200c9714fa9cd280b9955166e6c217edf2b6c247a06a541132ab8888a318c5ae61bef87d4065224a7ccb7b86608a17ec1c68b0f9df462251decbfa43a4e99fed6e321cb254d989ee7eae61266d45c8b3a8e1234bff14055dd0a86c5341f47cc2d7535107efd425515530b6f9a63180d47e73778ba3401b007b722112ddff7eb0b72e05171b57e84c57e32abef809d38ac14c082002553b6a7cea54423965255123cac04f17fa28ff6ba3ca182dbeb01441e2aadd0012157c044885d90e31b040ab51e3615dbbc085d44bf9084d3f60a4be936d19b1087625fe2676404399de390c67516f64d224c8fa8c0967c9ddd6bd92d74f6c77bfc6620334da46895efca07d09076662460282a0ea26d3b6f71221694a07084694615bcce9b807d20361c28188afbb4bd27d3590755abbbaec162bc9fc3de1ad549669f204978a19920e7462e33ac0a774a422020a638e3f0e149aa8ea8c6875042a407da5297088e5e3784f55f6435019656f500821e2b911e5eb83ddc6d9f31153d118a285bb1a243e7e9930a519bc7b9c837f3cfd75452a038a0228634404435c9bff02a068c261dbae38e2b7dc80ec02360c8b158eb2822a684ece40839c377bdccad07164787e9b1e4515eb3b8ac885eba153f0870c2a11b17349d50577428562b86b68d7edc058158cb2d7b9d0a2385c908bc0ef78e35ba3690809eb937e06ab7dec9961c13b9a3442b29e2a7a5a3c3199b35697859665d283a2b8f19b725c7fb3014f2e1519a25d09b6a4322b8553e774f3537a06768858d6afcb1bfc795125bdc5c56c98074569d3db19f18b6f1c4fa4e6cec0982cf1b77793efab697855dfeee6be9dc06e910e8f5d5ae51c91793b49254ed1dcb95057b09ad45c40982e424afbf49a1bfe2ed61c055d1c5677eacbe0be047afc7123382dfa048badfa49a2e28cfa92def3e52bfb4ef97d5d43360b86ba2ee7b7ee3c9ce271cf2efcc95e80d3adf405e49a7696b70d05a1603574f58d2487a0bf3ae312d44701a0c6bd78164032b4553e87af79e3b75b30310dba4443f692a45aef878c742fd1eb69839f03edd15a8645064c9b3d24649aced6a751827401265f58e5ed3021824fb9535dd8b884706a2c0faaf37351fbbbc239d031636051a5f7a95df747701c84c4b440c2c6571ee7ef1658cfc4427fba4951e1c9c506ef15b3f98fb8bbaac3f2455e94021977070d1eda186453d515245f5d98f4e3f1f94cac73340845baa4d0abdfde29ddfba2e5fb9f6219b7bb468858efb52b033d225febda69f9091788e70b299238ebb8d0a133341eef630c26223cc59194b0ab71ff09d66dc847155e486d2c7cdbc8d7f31b0075c59df1c4f25b1a1633161eab279c96768dd341d0265a61aa5d69e403f3bc5e8b8c0e257478ace60a7ec557a1cc7914fc2b5dda07dbb11b10df7b3f28cf0f764c6d15a0ee03d349f3399a2c516278de3263152c76251c368bbe98945bee56033e83c8433fe3e3c97ba8ac4a07c4acd59cda73c6f2e0d894738e6511154dd358efe05e6141f0500a1dc84257826134792752792398080a92a3924b5687d9594d8036a30f23d06113bf8af7abe201a8512bb652380dbce4bcbd0c0201b7e52e9321d895c049ddd5c8575ffad500447f14a9cdb24a10949b6c58d59d164843327de2bef0daa5fcdea1fde08e4ed26205bdc962497dbf635cd06f3deeee415542889a3ed95dd0fe5f9e9181ae642f2176ef1c57924dfb5c1ed54e9c507092772fa15e7a250143d1848c4b40a39f201686f8fe1a0be06a6aaa12ae569d2a1a0126755802a79ffcce7a2220e6d3cd10a002089d15926542249b1f34164bf1b2d114e2737fd42697ae57cf1393815984f3dd9a047c8d0803fda8b24be3f2d08538a87ab099a487067407bca7154e2fee2ce856045b14f6a4e59bbf2af55ff4576899c40c67324f20ed5326ea55e19be8932acb9cd0102d8f0b369c597c3831ad8760a0dc14141f77902a1fb66f867c7f8965d42db9ebf462ad3b3bc0ce6eb489da5f8bd52c882c5bb2c07cf7f41c960e7e66e6ee570cd1196468c0103fa688bd0bc29c54f9410a700a8324802f6b0aa958201179edab895f2faf8ac116c4449ee2607ba0d45ab2d1ef26732aedbe1a1dfed8ac2cdc79a6bce25e8f5def606aea626fc2226d125e6ee919c0cd5d7ae62a549233d55372778dfb5d73379e42046f882f9804b328c81e877d0abed9b1524974d9016ae257c57b2c579cbdef6ac209d422d9ee7f265349d1b57a3d00fbd18fdc7250b6b08c10bade75d775dcfcba564e4753a0ccf4980250dd0b1dea1e3e5cec93a60383be39a0ad9a8d420dfbe6080da8f769d0bead2edd9ac915e6f691ac0c9cdb1fd914b6b41822768b749a4d8d10b98bf74dbd6aee84f8d1e68e942728ecbffb02e61b89604c28e27d73db86bb336998844e3b95f6db2fa321d98dcf1e38952381a5ff0da2853caf41e8e57d7edaa888e84d582cd84deee0bf1428ee255e95db10ecd357eb4f0fe1550df002b45d996a956751f61d714f203dd48ba1cca55860237043b202aac4d770000585ba504f19c07f05290463cb0c8ba3f52b13500f6eca8037de5e93006764a9e6b923c0d56fab2132275474abab7eb07e3f04964d7d9c2b95377889e6d122b669355914b9ef1381617707589534de1c7233bc97b21944a252a3aeae01580b12e5f3230c2dc43a1479ce424e1b0afaaeb0b6e3989ce7cd2353e9e40d2ada581b9ebd1cf629eac356bbe7ff30cd63fe447e623271392ec0fce3587a498d3fb9cae75ca312812d7a76b7a3f763fe5e4fbd370c592b1c7e882bb2ad05112abfad582db04a40833ff20e59db8a407f08407a8ec676e49cd331753365df83c35794817a395b6866aa28138fe1f28ba4db7982bf2f2ab9cc2f117b3a3a178fa23e72eb6f680d22ffe2e65bc283b9743c4ba5428c4af6ff41339a61e973028fc84fc45bbcef51e4e017fc1951cb60ae41bb7b89a10fa457228fe4f5886ae43ca21acbdb966d2922a8363ade880588a9b95f53612c21b8cdd1fc6d34b43764263adc20e6846f28d027898bae7e9796a92dfe2f03461e99b2c669b196f04472a1a45e171b5bed0e47764ce6a8625c0135cd79a38bb726c2e06a99841d24ace77c38ab6a0851a6b25b4cfd33766cd16f40f5fb367902beba1b34e0df9d889403970b331c9299b5e8edc8b74158c035a1527ce9635962b85b20240da41d45f02f295453a95f5099baae4d31ec9f67ae223caaaa37f9414fafab0abd7e75c2b57070d903e6657a32da896a5bcf77cba465d1f91eac07fd3deead69ea3c276558a689f2f52ffb9ff0cda4e96d7e8114636bbfc3b876bdb934be0bf19572f162970c8a18b953c2d0718216d1747be076637fb5282100c2d3059027cd2a9da30d06000920e446fec51f6da5fa591ca5cc3444ca9ef9a316e4ffb5193aa12c5bd5af7c18d04539c88a8ace5ac8e02873be18b90b4da58bf15964dc5448a8d14abaeffc56758532a7831c2b368b799475f0e9d0f13789fe8e2cbb45d65a6594dbb30bb37e900d2bc6e5e5eb6ced5188873fff699d0597d333cff9982f7e2c0e1147748dcc35b931abf57f4cf049064e13b77159dbb205d6f74b4b4941b65eba2d3f228c43740851535d51dc6d41356b6acfb335083e2e0b46a208a37d0f52fa127489b3409cec374ef1acbe287b3ca63b162e318075d9aa669c8e517f2982dba86eae33736e6c585efbef13557910782de6ef12901e8fc3be0432e501fbfd0e8b02a2d4813d3fcaac8006f07bcaeab4ac93b395e574a43ccf775a72484b9f871698d7e27f195f710fa3c2928f3b6d54efe816c754af99e63b4c257c066ff6a3977788c77514ba667deb0dd18b7384db58379560e3727aff3acea0265429a9b749bfcf57c28f4efdbb4f6d551c1e566134a64ecc8e7db8861d231127d3cf1324c7431471b0707acefd467bb9ab135b56c912d3ac17a8357bc7f961e9a3782d6a28ed5a7ade26332b43da2875705d41708b98be8b63e262628658ea54b3dfe8c4d65931949f4cb06076f690e06c9e43123d7c4e00bf86571dc3c0d84f70edbf27aabec9f9c1446bf65f78b90882cd768973039962b298aeb0ee8e4c148435244cc0db5f2b6973acf07c2665eb65bbf364143b292f320a170c975c7b5fff63a1487db55f34c50c05da0e2d7c964a05afe7018b9c9ad5328d561a5f58bdce54bd1173afc071163d73762c141f84416549763e868442388a905e5cb375fcb76817eeb2bb86a0ae5bbcee185b21b6e6187e3e7a7ead1ae96c903521ebeb35a79823f2997a56bb507c21541d517be8fe3cc947abef9bef46990fd52daf8aa72cd2e3110bafe23c7e9460336976ba02e9ab7dccbfcad5cc1253182862d0b24cb57e444797ad74c2ff2bc3c051fd32a55a5a52b4bf9117e50ca8a58abc488380a45483bb4b6badb17982fbd2497e9e1f25d8985a82c073e793a6641e96f708935c53202dfc3e4c0c581e7531fb18aed371a2d4a0eed8fe97a94bf034f4528bb7016a3b82660f7f392ce1ae4b5a125e33643988b49b01283a3a2ef45fc2fc90690113ffc58d2bc9033ee5176717ccb2d396fc51e6c00a762a4857af46f4214406ed6a1ccd543903eacf55aa04392192f882f1b5f01abc1a40501aa86f896542fa1832e40029b56de89d701fa3bda488be0f4451068df26e29e6c0877f5ad9d197af38a62ddc8e8f9b611644f6fc62f53b677f409d22600bf26ce92de70650da0aa4add6eecf9624f5a9a28b6b11c7297f7b99863baaafd03b48a4a3eaf9dd025f882648fe8b165f26b4d5d8f655cfe6462dc8fc4609459de65f091905688900089ee00535dfa400d185737e29fa2e169b2a6eed7c91ac49d978c596533331e87caa2a3a32b7d808d2923af09aea12ae64c6c739b3cb19c3daf5e6874a1e83a1a1949759e485e64873e042caa588f7d7cae04996798e3545a2b814de58374aa296c0e4ba9f36b913f728ec17ff4d130310346a29560994423c82ef234b9f814dd2c755f1628bd9413b1848b87cbfcd6379d26becdf9eeb2f84372ab94e8a0ad539eb19b77cd86c02cfc875a0960b62d421eed71a5444e072b72b609570635bd917f7234a6c67b117b86ee491e3a6aa008621e78df3ad6d7ba43f8d159931fb887f45fb4ee7f8a29cf8af6c53a4444666f805eac98b55c0e3d6c62d6d9c8845464c22c05ff7ba41cdf41f2b630c58b8fb28e3ef13bc687e53e59a03fcd07a58ea2f71465941f44aedc9991c8ea1290c9f90de9fef5bbec430f715a7fba967c39c333a342f634a8877c82b6c86371b593740b14c39e772afdf5ab8b3eb5c27a594fffc78e02bb2870bd4a39069bd7fa71017e395cc65c4aec487389f93bd65e7d23006ceda71fe149e3101e4b4b19d8fac4ba4620b7cca1d326232c4a50d5fef6ff90873609ba5d65ef2845cab72d8223b7867bcb409d7bad28d65cfebbf7bda7723ddfe67a1f42a3f1b876f1dce9c178b68e4d8e18572665141f08fceb174a9f6c5386b833d5376156a0a9b501411fe1da6f15969dc19e2cc2da027e6d3f13ac81f7ab93d8ed741765726e5403e038c61162430c3204be2d19873d520723e4c6eab57d0d2cef85bb8018bdada29ecc68140015f7a35ed0ae16c4a5059043c6c95542b454ddd7fe70a2108470e8444af9e4a195997538965ddbae78ab4478e9224f2ef624e4cca9f07c96467be9d9a6af91f89464d4fd9d68d8dd4f993d8bae576336f1a7afef36fe91283a43c5c9246475f8d1aff881ce92997e040d8d4f1dc189fb21e7fa8acc12cf433c1a4349532356bb47a4c56393d2b06e95a0616b20650e12f783cc167209255ffcdfa0f47e37648141f0b2d534f92d2dddbc9dc2aa0d86b8d14e4378d4af7a7d4f86efc327f152da1756dc89d4970101cb2dbafac097088fd3098450f01060a32fdd89eab91eb964e5036caa1a728670249bd4e518ae4fdaec4b74b4c5a603cc410180c4b1c9f5981c206eec9ac435094f2b051534cc85a3d93c018c0dac489f2d7ed0cad636ff702ebbb59509742f69817271a2ac890441dacd1808ac93c08e3bfe02731262baacbf037233b6c23428c5dce5d88de1effa290ec0f1a70d71dec44d6b8ca50fb4d839ebe1441e3fcb18766b1625e2f42a8bd97bb9e406b20bd709b4c1f8e2bf8f20018338e1856e8d71ed522c4488086a9cc2d4f0e450314f790660b974c277c183f4db031a87cb71d63df31d39cb9834b57bd71149695c6ee90e235d6f9133f48a8b9ef4c52b441b968e00460ad532f25ce5e4cdb99a3d143b119d694dd28119b0875f32db2ba9f0f40b511bd9ec2241f9c767d103b393b82569b124693d588763e0c74bf1dbf9943b4c40388d325e0d7b8e47ea94fc8d86d7c166d4b3cf2bcd03d7574cc18ddd32c20b2c7edbd929e98b0c71283d4691af091f2d9aea71959f12b1812bb4367988a5fefc25205479aa5dd552c1e3227715ec8a90c29a710253bc65b7308b20063541ef753cba072ef15499acb8cde3aa7967ee51144d5a52279fad183c689a2aa41e53cccf2ad19c259c51d5acc48c9ee760fb268229f8a7d84050928f22254fc4f9f09d1d2821fcf1f35764e9c963e8e048a26ebce279e18479ae3a537ac97ef560e45453a9d1137289bbbac7dee897e87b8e52a54bdf262acf22083d41b9fbde0be8b5a7ff1e9b4d3dcd7249e404bbd15d94bbf6379794da66e2f5de5dbaac55b0075ebbf2234823b4bbb4e829d18f5193d5bde2f3c41bec0b3dab1e81e1e4a61d693df8aac0150819265cca9aac1cc496fcaa293e0dd396621b7541df74208999ba4cf4bbd40478a54f0457a2fd7eb56c0650dadb7a4399ebb6163ed1b785ef96d57c67bf780944b2014ca7c2bee3ad1cffe3014c39e7835029b1b053bf74cc100406703b61e7a927f85d065a6e52c66a3bf5095e63552f9808c5c9ef6fdadbd297e489064f97789dbed4f0cfb6589552a19cc8fca0685f474eded78927fc138d54e91c654425f344e5d539c48c415c0848d9c444e16b239bf43fdce61b41b6eab4fcdb941b912f2a5ddf8e29e3d589a443cba60b9b055db06aff63565721d77321dd3ba21302c1500f9be017e96c8c4f54cdd946a7d4bb5578af345ab7741bda6fd31b7d7c1f556f945941974fe110a6ebb20b3daec5651e482158f3eee3ddc8c5118a3397c354034d7ef797e78c1bf6a7a2b084798f652024e76acde5b7645ad6870018082b099e5d85ff471a51a11e693b66c905541865186bd5307d92f7125298086baefa225ced4780904e4b85d6c488c80c8fe4fd032fc8ed78eed68e28fcd356b815b470faee4dacc1eee6338b04352a1d2d3a3511363dd7895146f13b008cfff89e523a46e7f0d231a872390f5d1a50a92c8a9cc82d407c3cc05ea744beb07bf3046b70e2ccd58ffa8d516897ae2d6b34078c8ed9e455dd5c8837f8b31dbd9bda47071d637d40d229abdc08dae4c7aefffb29abff83f80906bef1a8a150d76b0d28beece626892b0f5ebf74d5dba946ff00eb0ace4f635377bd75a513ce7983c9d928ca8bb234fc3ab28691c6db77919a50ca66ab04b76d1a9af3b53db90951b60d4a278d35835523f075b2fe5349e4e2de351e82c20501cdc54439f8943829cac79f6f01c6254e3e6e86d53c490e73046449a9e8573fbae3290db543899407789f345d72fe1ad37fd5639e71e4939fd75e30e61ec4ffb3bec1a55d86e0586f4c7dd8ae80afa46f9c479645dee4bd849a8a75a2a22608cdfa558e3762c0ea9b8316b3ba3166c30c7e428ccf6426606a2b87f2f3082cc1f4f4d09cb8b778f17376bafc5b3cc8c105b8c8e9431ba68bbad76ae329e1f14f17e7f8955310ecac1b6e65c7e661af044ca012bdaadb69c4592d8517dd4c035e5b78a680e6aaf468aed4afe911c3c88f8b3ee199a853189777d78e494a48cf780fb9d12e3982f55ec691c41f489c95dbcf615841061d39f0dbcca51534242a86227be9e285a5919f116cfd033c441b814ceefe75106b2d32139fd1ac33e4add31d185284f4f88d8bba66fcbd4aa28c72ec761c758f0844311110100c1600cdbed64ba62b2e6b536cb01cc7b307ed75f2f10eaff3c4e0f81e53d75f9b70193c639bcc2a9e6fa13b7e1d9151791fa136e95bde800860ac5ac4561feea8d0317342c105045eb76b55c8c727fbeeaf647377033e4bcab05c1f701cdac35124b63be77ebebf975a8b50d89e7e43743bd3d6cac07ffba16989d4d7e84abda24f202f5897234fe395ad7be2ab97a421532f70e11bec02b522c3edee294d61deb36004ad91c8e4d00796dd36d8270e5a05ab4071a116101d9cfac7ca8e6069902b792b420d089871710adf0439ba6e557c2d8018887a4346a6a7b13444d91ee5d0aea46a24013dc83879e26414e70e4c906da2d430a16bae8fbb6c35380c0edfd74dc7f2fdbc6822b4cf75528d15f066016e206ac72669cc2b1c10cf0f0a9ab98291c022c5ca3d77e0441096acf225e4666b0ae3170db9e5827271d90bab6b0b721a02215491296992fb78f9d4c7a5c3532b540e92921055c6aef76c29c192c9eb8bc6268331524d764371cedef1d5a2710d719ed24f316971a8df8f5ff0ab2a256ad96828836a2a4b5ebdacc71bfac33ee66be475a7e137df8bad9f4e9365369ee585594e141fb30deeb1c39658d56bc34fd4d0a16b345443caaa9194dddef0d0f0169a3952f2c2d8c068952fe20ef90e52ec9f7b6cde6fec336a1c461ed3d2f3e56848587f7b3214612666ccb50450f4c1d7802ce3d6fb124b029f82894dabf4bb34b6c3f9d8fca7e1d1d7400893f43139646456087d1b5a04fe65e0e41df953c65331d357c9a775c2bd2834ff1c8c6ee3d080d23d7a9a838f5f5bb206d37010123930df6e11a660e4a9ccfab43c72168919b81646b4a724ba127076f00705ae5c0a6eaf42f74ffc4534450fbde2dd24cb934741d51b3cbe655acd379e8bbf5ede4b14dc8d51517eb9f67c28f70fea3c344a03626a5ddd226597e8949c961b1dc3c9b4e7acf1cbb76218626dbc8d6a7d1cbfdd02d9eed9c0d3a5a31ea5327c32c3adb5b1005a1aaf78db0dde9c4353238b44aeb43bbad3aaf005c1263d4c4b90a270398c5db9d2197e927bfe31237e0c98fa00b91f6f21369df660d134454d8bc53f0900c75656570a19929bd0e380de3b2c61d7a9320d6950bdd931a1dced8521bf06093ffd0fda557a97e44851ad92e0e792acdddf61f01d693ad454f9ea475d1a91fa932ce68fd30a3e404a3031eeecfa1d54a884df346e3d9f3e8a2b72ff0baeb58f681c48329104b9fe42ab720d7f1220a9f893d19200c1f1319596fc615138aff12c8fbfefd71df129b872dd48a71e90ecce93568a7640768c7fd451f450fc4c96b561fd8979fbe81f6ddc47871cab162211d8ed651c33a8cae4e6e9c81a9329b9e152dc194905363138317cacd808e5395f328da530ef0b63059848f09e484b5d92e42bc2fce8183930fe685481cc42f8e3919e5f8f4fe376daea6ce6fb36eae467bacfae0cea53e5d15e8b10d62f12206d23d81efeb9d7a0d43472f9809d8d161c8d8e21d7eebf787692bd53d0071ae7d64fe6783f63982303919624c94eb9d3154916603aab2ead69e645fddece892109ef6d280ebfcdb152d26be68cbb08fb366496ac8a810be322e101b92f754cdca96b17345021ae1540bb45e37e26e89d0517e9067193ab76493f10c350a26b870cd5ca0000b0629f3df4a3596f981f77fbb3de9e704ac0a1dcff3652eb3d7b59c7cf8cc67bd4fd8c0d35b73c27b765f045411113232e01cb7ec79373fe7c162205fc4d450b6c0015280441364db50c1f64efceb11dd3b1865ebf84d56199972698bda3e46686e16ac24697c22de77b56bd2f77b4458230fcf88cf4a13f211ed63e82d676d9673aebb52e91f00024c9378dd565f83ad5583a19e2622fd30025d83b7022534b466900fc7225503d863663155473953918907683c7bdaf623e7306abd17b5552163dae7eb06574801e8bffba793db052662f2c326826489e5b45dbd1106573388e89002d4295cdeee8d78fd2bb1b6311637c549904e39c913a02d84a394ed98543cac3572228af78aa18b0dc17db44164e9fff9733363ee55dce481f7d2111dbe7d91ac6dfa9d444e271ef542eb560eac2b3b3d79a204fe4152a47d0daaed51a6e75d7436c1f8272def6816f27d06781fbff386fa6e0ffaf11bc6e792cda0e13807f5673563c2ea13aff6541163400a77216ad27239754d70d57a6ab229d33e79d18b58ea6a58d81d30a5eb391a88da995a6f8babb1e6af05c7cc9e0f0be72ea449576875380e031f1abfa2ca1690d489a15fc04609e981178c5dcc7fdf32aec96a1b2a36417c74d876a7374f2438f87b5a76fec72ae67d4bc9820e669ea9fa22d09916b5a560e2756d0a7d246b3cfc5d5073a5dde864e05ace860302cf0af7eb7c7ce304c3a7cc013974c09928dc153c35bd25678a39ebba466ebe49b8dcb5efbc495b81c8184acab57f00cfbd0c12c88fa46717d0eadbed3d7d61db141b0a3e0d887fab4b9bdd6cba2c975c279de2182d5057e1aefb388d76f930eb1836d1f1032767a6dc4f516c84111217227d484a6c205d7e881a7e8fc6954bc4e3c7cc7c8beca9e2f7f94df62bf3a089d749dc8929570ce227882907083a92948b25eff1534dc48c59a063e1bce6ff79ed9bb722c6d844dce43a8d323a7bccad7cbf75052e9c62e2d2bb066fde865604ac25e6c2d2b7190256cc03c0d8e40148f3dd8ee74a3d626285b4e3492612b5a29428fb8149f6c55595671f752eac6cd2225c021ca03310a49027b4f64b0796625b106ce3e7c693c7ed05aef594593e940c8436b461712f98c89794eebce8eb0b7aa0936cc59f805b3e389599beca793148b9bd40b6c468691ccfa8847d36053f8a1d4bd577b8f4b75ccbe25c89f305204d4d3feab59b5a59d698f52d6036702ca297650cab2e425b176dee17c395d1b25ed9c190471563178f9c46201161fa57e8fa429e6701d907972ea511540b7c306c2825580d8efa83e9d5f8962eff2d1ac5013e574d980acf48c85b89193d941c7e16cd2065d4f19cd22a595b042edd8c7b6a2f5b938476b8c2b9df2fe891459c0caac39d718f52fafba01e4d868cb77435bb8993129cb975d8810d4e0702a582ec369afc1ddd501c6670fa2b808070ab495bd622e1642de494aba8e83328c39787f7d34782af5f29d167e704fba54c90355b2eaf84dc8a9e1853453b0c308bc73bc9cd296603993d634d74c5681cfbdbfa1271c523114aced3ea4d5354db9ccc97ab02eb93df58165417702b42061367e77f3eef046ab6f628a25c1ad9c0da5b8e2687e98ee0bc1681f93d4293f12437f8cd9e01a45bca8d6f755bf36ea48b1c589600c71d30588609adce7cdac460aeac7ebddf73e382098bc81d631e1f57857754cef01859c0dd89cbb3f80331109a10d31db13f772e566d3325bd98ed5abe436fe0ecaa9ee8d6e2b4d5841fe44a461719a48352b639f15845e0b0b81e068177161131ad92551badce3d573d089459b0bbff62150c450b1912e5b16993f6c7f022984e791144eb24e894241df1951fba16ff1915bc66d1d47c6683ab77da453082cdf4b50ca1308a74d31ec403810b8323468900b0c2552b26e216227ce5685cc472638488ed69c7a01cbe57efab5b7b00ebf6244c2da0388ff32435a62273f5199c740bafeb6c2d2f7689c303df0d286f020cf218130f797e44116f6176d2c08f1d14051bfc959377d56c4955cd4a8bb27a45ab7ecf1cd9b87d0d4971b666ad2f63c1d09022a050dae8f80df340341e0a1de101a5c47592d1d981f9c373862af45c2e66902128442b3614e74702507b0b4b2b3a0c82e710b9182cf62dda1d186790432ef894282ca901141cef76655dfa997965c839b69423a824d8a03e7fa07ca1b79dcb47983fc8bc9a8fe57525dfc57941c4e03bba4b6aea0e4ecb0bc70fb5641d3d6909a8f86119dcc7d531be1e643f367968a7f444cb588cc54b318e0efc2cd8d147944fb11fc9ddf4797d3132fcd20b6fc311f5c474f9d7f620aa4a5fa3b983e30c9ef2e85afae00ad1266038d65a0c6fc89028a75cac7cca26744eed8c4db82e4f50192204c15d448d7929686cff51caf6b91d4fb1bbcd97f97b110dff6c6ec604c6349f86176fb2df64a1cff1579e454ec2341ee1e95d6a2dd784123f07fb4791abac041840b3e4ce085a97439692b6d9561029ec8af83649c5b6d639f2192555215edb0890e76a909ce8f1facfc28d5afb37d2cfda470aa2a16559d48ddd9187853937f402591c0d9b0bccf6bd941dd3d94c51c1e9e097f592094f5b9306ca2649858975bedf9f3cbd9d2cd9d872449916ad9b994ddb8f2d273e6b4c1b03a6bd46249dff7ea3449a89ddcb36774c4ce7683e9583ae7e0c7c0c11e8b6018d5c6808f47b371a592df4e210372cc912e1390e77f7411470d5a9a89c73a9e506286bdc45fc5c8275f123dd2647e42404a7107233196559c3bf5e88522babe5482de533643ab514e0120db5bb468ed5870f6d16dc78b92787cce9f0cc9b73efbb12be53c56f3c2b7b9d2cafe67521c010e90105e763f0064a04adef7fafa87a2e24d5bbcc5c4cd2a03f2e67488176520435733b4a22887d7d20759630e88e687e854c0fef3abfba96861969e0a969d5af3b59fb0d38015563da4a2290d88f970c2bdbaa603030775756258a92c29586d2ce23eb408e9f7542ed25146b0c9aeacd15fd1e3b19f8855e45dde63a8333160844e90b946517502df0e545093fffb07d2b373885fea72067785fc10106fee35fd51f4b683b2867cebaa665b3e945b813664f52e3561a25b3953baa9f990e6d18e48903bf4d9e8c4771d998b203504b368f63e2a2bab2fbf57c0b03640007bbd0439c635e91cff78b225c41221e0219753b8f85314946d29a1c35099a2ad7b79f3be036159e93307a639751450bb8fb513df2881274a441dfd56799f2a4da783e0ce46f7f0bafe97c03c9d9674e4cc005ffc52b9dfa4a0c231e32c5c559f594e08b5336349ab370873fb7b45fe8f1ccdb4b3ebcecba430415adabf4283ee130fd481dd22814e4f10bc24eae7fdd50bf765bb489ff66f14a56e34e128db734a6a88634c43f9dbc1e05dfae77c4f8b323fe71f490c85fba82355bb17c15166d272d3288090af6483391087e221672ed6916f51a2ce9e66793d63b3ed47c2cc484189468bef4c2a87673a156256f527df3637ad38d62ba99c23cbd5c6f04b43018af69d268ec030c3fd1d97df334e56115f9a033b3e463db6cb99adb4401d0f60a015226783f81a1183b2f4b6c7d77a2d6842fade68c3be668cc4c6b41fcb380f6e2b7a55801874390e3143882b725fa59f6b8a5dd4953a2d921299caa3f2147be4921115faf137fe910e60ae9985d8a4fa65ad9b07e3c6d086b15658d7cfdc990e5bf3e94321c798974eec815fe13c5a62089d884ae957dac271261342ebf8027b6ffec3a575435f7995eef37baed84dd144e5d855d4b5eab53c45620c6f539151b4f90cc214db92732ad96ff5d66ceaf63712393903bd37767323afeb1c45f0f04139073f1e6be280004533500e7cf6a1fe94f5ff4aa2afcb73f75b372161c07c7dcc7c5f3be4573a8088d95ac1eed51b9536fa8001a2a4527452fd9c590d3fe7e745c329af9df6fe0f7e175cd6d21cded2f9e99a4280efdae0fa0c359399498517a9b09ddcde7e382053d75bc73537adc22fa8902fd548a2253f66a0a56a74c317ce6fdaed68532843ce4f74057c073673b2fab0b6df7c4527a14d3b5cea1ae4e5b4a3b43d49f04a2c6b64b52452ffbb08fdeca5da3a04ab7e41984fd1ec9513a071335096145717d6aea8a836bda547726fa7b5e43fce487c3bd4c02ea156e8fad0e29a0b6831be1e45827a1dcd5b23a48ec4cd899701bd4120cb22648bf18d7dae1a0ba7520a810f6d16f9c06ff8e7ad4f276c5e0f2eb66a657cc36971a9a2b4972354001d3adf6599acc4dc213a53c88ae41bfb03a926a872680c84bd05116f1c19b6ecb9eaebb9bbc522d422e6c279309bbc81234a1a8812914f3d086ad39188ffa6f238c40e9997e24262e8f72839baaef048e732a660d501a91a3266fa6a6e1f15ce99e0fa220cc63e21fd03b2435580b398fdfe53fb4ec02f8a9a17b9e0536ac1557b8c1974bb59e751ec28016bb7848f440a19a67688b95946f3df1939d2a1837f1c5c0203add5e26f9fa192a5b34acea5093904dca495f2b274d71a134a17b6b5f7cc9d0906d1edc4fe34eaacafd550472edbae2f98a276ec0d84c69066330a1504dd4aa1080b40246b18c60492e4f7bc5302a67cef56905fbd928280b416da0f203799cac6429b161028d118782284045b5e41ae10fbd9a653326327e978ede93a8cd468a9f8f047de10b06612189d268e37eb40bea382722fbcda4da861469a2abcbe164c45771994dfda583fd10b29f8ed27a7a2bf4b27cd7dc2757b6e7207731c7357e31f48bed2723ecac40093d534384a3585b4abfbf5c23a44b53525d4c6360c4057702550523acb1ebb2f53f827d6bfe7fb70368b7919cbafe9036bacbd0730fc2632dcc2ba052bd512cf3ee4610609cd17de63d521036baae77b99509cb2145bd80515b2e86566581c46ae5a651d1745f08c7555a7a80b9b058619a2fbbd0a170341724d93d4c4af9b4a146e9082aae477cc64950c456019f7c4078eb8ff88858f31a7ab9485fe92333ac19e2222d083239bdfad50cd52f1496acaafa1596dd8d2b563b5beabd8cdefb70ba8804c7e890d30a5215e73620b00082641c4a3aec46bc193c365da11a7a4e192a70d60e9f25991cddcbec840462ae6eb8e74a618e94193eabba099ddfeff9f28a5aa8381c46579b7f589ab23367bc7e44f817b50d1b5aaca2c244a1d6f4164da16a98c120914c8ab1100615aff7797f5a42422084564d4d49c09aebf45754d2fca3898c7552a1f5278f53a2f4176f5fb0471cee68ca41d85405cbf0762253da4fe5168e7d84032ed432a2e3a9084fbfdfbc85a6b9e9248dff9ce19460ce000446af5734b012bf6bd4781d8d8c7198016a44c42c34db96110b705c14e69209697b6060951a57abd0e6487ceeafeed78f66f126b12457e727cfa9e018d9c87cbe9bc83ea4234ab1252a6c888c5337998bbcb90aaf66febf681a5f35794b1f388c57b0fb70954b087ffbe1819ea64a1a73eb5662a544fe00a58d70fa7aef4bd4dc6f301e7ba56e74382dba0d856acbe013239124b92e7558f25e138286209e340648b1a2dc19f08c24a34ebe4743c49480461a23a7a680237c6f8cfc25534f40ad7ab61a981b8a6990c9ed518ea40bdb9e020398875a4e9795217010d46130e923b0a36cbd4cea3b535e17e76c0c1458806eb4c5353b2736c102ba6b2ceddb92be9c985a751b61b042544ca9861ec8fbd28fe0c849f07c200f1a2472b82e686289bfe1ee886cef33502c73bfcd8978823cc670d4b1389d3cc274e92eee6ebb19f0fff9c7d40a27c8e321c299c9adbcb0f1a7e201db0d6ca001b337cfcbe04ad1053e60ab55c5614e86efe6c7db065e24072b66c177c170533d79acbed24bedcba557afad61f15155138007fbcb40a3a9da2c3f5b8767f0e056fdb0ee92c353edc7aee95b362f0c964679e1339adc907be80a446a021af5eb6cfbee0c9416c885b25d46cdf35e0b1e0d4a0e89f948494a4a8dc7d8a7a61922b94495d03e5d9d4fcb5bd629544134a26cf4e6b57c3117208cac0b1b6a8e986657c5ed80aa31220da0d872211c2d59f325c332d145a271ad78e62b8e87026cc701522b6e90c1550ef623c25cfe8873b58eb15c0d9fc25b18ff39c14065e5ed20a98f56ff94fbbd600deb6d40929a6ab7084a8b2d8a676d06daa10986c7834d96928dce12d38cc73ea757b09e5425b28743189f92370d6ddd2d1d7f4f1adaefd5a04bb6330a57bb37359615086c391db94e672c39d2c67465cbcacad38113cfcbe97593cfc2d7342addd31b42550f4d4126a7c53223752ff600d8578c917a40ac219babcef41c4ef658b25a20a83dc290a41054f36c3b2c019cee968490bac9cf1a9995e0478327dbec08a227fef559a1a1f9212bec2f7000ce895336acd795e20f5b3dcaf83cf74d1d182f84a1a76a0115906d7f9e1cce93f0adf3d40c21157f043aeed67156fb2282c0071ac07cd6a8d247f178562f12fcc0b607a8c5fadf054c396bcd9c7fce802d16619cbaf0713e5ea0682fcd40083e47d844980658e96888661f77faeb94717bfaccde7d95e8809aa6f472719156dc2c28fc2601ad4969c0e95e461c92d0fdc6055d02b4f200fd7bf73d6356943d820e350061d3f9e05ba0ea0345671b520e96d142fea856e8df528d8e1c062a46ba4706fb6190c76142678df0d7758645840e67481a3811a840f1262f3666db38fabccb02b45895dfc4644bc4b27b4706c5e463379ff26a0a24bedcc7952e7363772e8765dcad234d12b3dadb182e22c1210b7bb9b9382030a19c7d080107bc4a0c7e77df15cdda054b5c27afb884aa40a33025099f685b0c2760d259ef4b3491bfa4dd0ae46fb3fe91fb41ddc1f1ce93580896b8c84ba5b91ce64b6c7bf651fabc724dbfd94e6880b4d2d1d35cb05d0c31b8cb2e74fd4cbd6c071cf2c6ea2a79b0db1b1409658d3fcdb106c837892d24971f3cd6a7f1651e425d34d17de45992a6638d08c1552467fa51693f452e2f84fc3509117a83cb4cb0d3da88df1edf18923bed18093a9c2e3ec6ea32e40eb72eae9e350d0b752fb6ee771859adbc4467a8924f10028a28a530444ef4b80cb1c93af8cdbe389734aeef382b821594e3368c15b420412550cd66c6a860b2376477b2e5156720135cca463657216cb705bdcd3aaab40b93cce222ad4642d6b673febedc8f6565d05d6a675e599f2756f3e0c1aeb02090e48ced0574c286f1c7ea5f733a75754f7c9c47f394efe147b93e2ad4955d581e1cde6fdccf139674d7d00e105a9ae83fa0c094a461d3fd37598834af7cc1f86f1c3427dbf9ffe972d74dceda7330c146b9411388dcf3131fbb35b8cc96cc438c8363822b357b076fb7cee466e7e313bf472f00b0ed66cc9e5695d5cdca52c247267ee64b66599d829d22df63dcf8613cf4eb3619971a50ddf0ee2cc6c84bcd743ed7d2741f0ff1f650dba9a1a06b3ea6e28d0112dce2efc8cb973dc87b4ca8edb3b5f2b053c32c54c4f5b8157f90b66fc064d01729d23033a5f104635e043ab9722368b4f71318284bb46e8fde8c63bdc39c8cbf9b5f525bff1b6fa121398109dc8b5d7d2d0ae6ded706fa03c60443a164eed5abe1c2a6647c786d90c7be6df903ec362421c17e778010cf0559c2302d6746f4b0e91a0d773d1baa15aa2b70fdb5cd518fa1b1fdb626e2c73bcbba04347383e43813795f0dfc160cf84385a874e0c0490ccb1547f7a048857dcbe81393e3176d43a67c408bfe5b8450902754303dc4e7652467a4506fd1152433cc035b91faa3bdc64321022194c4a3748e7bc8473ef3a9f4b888e2f4cce27d2fa239858f9ed9e4a9e81ddc921809251e7a7296d3b3c4c63efb59b4c3c59c6fcb4eb79d335307161d0bdacba803188f2a5cd7b453c507594ca36498101f2f5fd8177767979cb8cd6e86c4692206b913ca49f186b0789bd2ec2866ef8309e13375741d0763619aa780e41b5744412619ccfeebb95197c4bf40b4522e11823c40e241aa23e17aff18b35cb309fd72be4e34628698bce3680a77e2fa36d535f8b6da5c24c488abd2d6f43835f1766c12fab8e52f2dedbd6a94c80be26732e636c118892221257f6be1d2aace06ac1e8758e44bd8799ba629d3c2400ad528a70ea1d596994d54e2384a64cdc1c77a2db740fcfb2f8240e1a2df91bd8a937b43886c16e1f407bc3e86e4edd8a905f6bddbe1ab5b69dfb8009557b84603f94665ecf91421621e1698a62bd6bce73fdf397fcec8b4e1cca1741b784adc43f51556e132777a68391496b4f7368f5a5b0cdad936135a4bd936f34d216dc887255d99c440a1c6273bfb182c238444acbd71421a2d7141f17e3006d6041451b55e8bec72fc446597d3cf4532b50b396e58f6265d8ed8037d752337dd00765c123784a9201eabc4ea14b194bc5e697fea25bc3b410ea28ce72e021c9d6f8dc6ecbe6178898e7a547de4505d8fc6f3a2e1184ed2058142cf02542299440e91a7b99f6ea123e13e13b29705266b1180edd244118de840eaf370392b97c266c2dbb74b1698939773766dbd52f410cbea141c781ab770846c30888f31f857e973efd6ea079e4641df6cf9aebdaa18acc61afe5ef08c6aed31ea9d0c3b22354df1fee24889c7ae936c846ccfeaa2e6747a57fecb635eabb9ca0a6e17ca88e45d2168548022639c407152714c24e96d7d0169587d6aaba362d9c796a9d4d8c88bb4ce84ffa884ce0178dd71c9fb9a8899d31fc790752e2a2fcbc8de5f59ded991c32a3db94a26276211d81325130960318cd30b067fc1e0a023414c1552dbdb4a8aee6621cd1d033b68b687400bd1455e8b1ed896f01beed1ab186ace58e9cab7dca553a6e7887e62dd58cf2524c8dd2b438ee0eb82df5493183bce1a5d5f5ec0c6032562f788c62659bb4cb0dec92de9318df7e71f3f3d666fea5d7b8b7f652fffdb571939a76d3cc2aa13498c1949ec821668deadc02efada010b34a2ade1c717f76a78cbd4dd42587d66c4382cffd866689f5bfc93f4f1041689a35366b4efdd70e07a3328717d223934df6a01c291a67a0a49a31ca23f954b973d7b6b85de91fd796ea89ad181b715d96096326b85c1ca77ecba8e055c31f81abee1e76f7622528daabcb22462d88cb278e3b6ad958e99fb97713f58c1231c6c569ef37b75531bdde7f9f481cb5d7491fa9a61f477f1050f8febd37301b40d3046ec80944ed768040bd9874dcf37c9d628e2d1805d8a0ca7a61714c2741ae999f003326d97747c1a83dbca1d7cf0fc0786b85351bad9aff66084ee958abcd9c55b118740486ebd10849844c8c901f79772656b5a643a457ab38840cdcb4ed8dd6bd8e586b4d2319149b47a081fa4240ca62bc56f5254725ce6bdd5768e0beb51f0685b6906339ee3c9a531fa7388ed100837847db1ccb4926cdd6453def06f45dec477746319090a92efb4e7e1c26cd62ebdd0b5c0734e2b2f78ddfa43a02ae87f16417c2e73f2bccddec0dc585661fbf3b3dc6916f22ce85674367f6569a6012fc1d847af86e2bd7654104e5cbf6647338cd13252acec1b62376a81d26f02971c00c9043c16c75a161103af3b62005116454a7616a163dfad373f78f2321e648492d93007b51d002c557012c70a2ac27bcceff97bf3e6235e51b4fd71f4e926ee3bede447738a12b65ba0b705f2c4639544fcd838b541a3295a7880be787c4f1d2c67a940a27d9b30e9e407a2d800a7bd6bb5ee586ef676547d2093eb2c14032e2eebf05a24e2a6305b4ff206ced0a0121e9325fcd357a3565e6c429591e920f5385e71a31589f76a7575907c92fc0dfda6db8796913ea781052c9babb76a219295f5cab8474e7cfc529adf3ee4afba43b245d877079f3b9d2a9959af152701140d1041914947b99169992505885f02dae67c8c569601dc57cfd98ab81889bf71a3a0d398fad2d33b394d0ffaf1449e5baf204277c9d67b5dd70706883b17f53058fb462f20d155017099d251619f000e8563312578e6df4f3d9982de8947d9d02f79820b1202bcffebf1e9ecec7f88f2fd8a4f6ab1b6c6c9dca2812593559b72ca1fba7dc6d9ebde584d8a63ba4b67cf5f2727d4fa9c2f65c05dd26fc6b8ccd6ec7854cb402b782cabb39b2608ba55591ab38a19c5a7026cfb6f5054867c9b333df8780104e5eb6eb1b6b2243918d512da11fdb3fe72f3d12e920cab1914101f113277925879350200b0190e1742268192cdd820f50c0ee53809103d6ad8ec90524771a229bf6157b8ff9ea855ad872c5a9b2725f20081d17fb464a5850ee27a95293f47d15c9a9ebe7f80596aef61018208a36432eadfdad84a359674425e6a439bc864eb75bf4b7b8e0e8c6f72189ff2c4a64c95dfe92155e0ccacf0c9ba456d99387f2197915b5a4dda2fbb0e3d0b07f0c33796e65a6d19dd2a27a27011f93ad8133f544b8561a4b0735f100a8733842bc16b1c7fdfc6691e2fbf89a6b10805ee1f78b5a772b1e8167587bf32af30703e1fa5648e586713bb754e8a866ece058f81e39e262354aea6190294568acb0f2f0bad2d211f4c30daaac7a264733c456833203cee641696f2ee8228555d1aab71c740e30c3824fd3684e531bf47219e0e40816fbf155bfd5c6929d34a4d0dac08f28ad4ba20f25c7f83ba57a0a4ea34ae58a11f3516fe43e286619e566c7d5c2f8d21e0ffe0eec8925b9c1216188d0f1d5e037c9ccef6b44efc92430ab2460d6c6acc9df7eab2e5d35ffd06a41ace8048d8186fd167d0b8c3db0fcd7d949ea72bf5ebc55666d3aede95ebc30e9649a8f2346cf8ff33eb172429a93c088e66c9e1d03f0fe0d73541a0f89e70893915d6d3eb279fe8a46383ec54ca67252caaa2c99b5cf066b6560b0d99ae7e8009d1cbee06dc8a1664a454ce5fee9afb02528ae1ffe6366b10db3fe876021311f692904798ea615d7140a70da8c24db376ab53518eb5c9b8b5127acbe0cab49f87b76cc99243fe3ba40a8280fbfc768b93de9b98c59018c30728cb1054d23552e141438b508fb839a1440565573a672f1697e4a5867ade1dde0520a53df303931ef353a28cb2d7b451da06bd560cbcd0c129ddcd0fd3919636a0ed54d9b8392dd0c67bf7d816110356a1eef1ac4c35f442ebb614e07908a2286ae940e4914d24a1c79a6520d2ce9dae552d0f358dea00459ed40d3c0238fc2493bc02a29262dab381ec072c9c48fefa1702e0ad4564bbb61a1ef71d15d35e677842ee7f17e6ce7ebc15e3406a725a0680148bd926e8011d904a3c0f1cc9d4c7138b3d41dee943582dd7b75889ced07cde5ab64f22c92fee8cbb7e40a4e3489f0b4c4a208ce570f5517dd1d1f5b548755db0ce93a887df4063c99bf2c05598c8886ebef7747e8782cf0a611176ca9e077881e870e195db85baef2edf356ff6695231a415d511766149bbb4b4e3b0d0249839c7f144d03a671bfe24fc481176bda6bb809f9a5cf28be85f1e6a1a47ab07e64eabf6b28d59ae1d20e7327fb63f842ca4a2bdb0e509032ee37028b2edd3009563829ebd124c56ec2c2444c302165121c46cdec022dccd6b7831c02960685c806363a6160a6296a691d4b009ba9c6ae7ed558f1b52d9f0fa2789372980c073a11abb0ab9b1d24bc270ae473b4abc3b1044a64b2d0786af5b9f8526e571b1a7f3eb1b060786332593877cc227669a58662df49e22bbb0ef5358d9ac6ba800d4c56fcf1e8cd71f1e72125bc25b0ec618f02bd8f48db3ff6ebd77701fef48cada8f12bec4f40f61ffaee0c55b4b7b7a182e548eec9445cdb4c0b5ba93157c1be5ac9ed51ea2fa8d5afa02d967701341be85f649ca5a636df97739c77fd1a382d8970661d20883c2c9308731f46d43bff5658a0c64b4a4b5b8d9ae24763ae5cdf4f8ef2ad0d8aa3a4300d0a5a504daca02d9ffd0d639bc05f9c4c014aab3f92551a9c3086c5b65df1bef76061af97d5ca1e575876281b2724ffa5c62e57c73c08f784b6e5910d5987dab147d58e97d9bfbb392a867b302b60fd1f65100d63aa0eee15daca233a1dd60089409d0ff9944cbae3daeefc8bb8760069ce677ea232aeceb4057be4f5a94dcf9e693741520b98fc5622eb5a1636a747a244219e02654a88fa2e569adc3c39e0115dabc9424474919cecd60a890b5ac9ded02ede6be9884dac3141676f725e30f6a83c3f9f0ec152c76ade1aa06a8543124cb47eccf6ec85ea67d386691c3915fec83f86637ffe3e30f1c037e6882325e86f859f2789828f54ed793cae4b39a33fadb3e3dddde12bcd441c099adcb0df0f5a71c7afaffc26f5e05a3dfdb752ce0f7c52d737598fccb0a71e68b848a0a9e1a7990823fa6ff3f54d24a56479609dcc7ad288ff20c58ef14557e2e3ba9df50807483a10da75ca30f1157bd5c850b641ac853334879c64195ef5e149697912c0eb4948509fe1cd5c5cef31502b423614a9ae4c332fdffcb7c881b8eef57f6d65dbb7351558eff3d51f051609cfd75ceea38e152ba1a2b810c92b8ac0458b406087a65711e3df6bacc67fe553cf46e8c64fcf518e86c8e81811fccf1404d50bbf539ed705d1a741514532921fda99ce49f27380e19f51469c07030abc427350d55c4a7f36b96eed033f94994469ca825c603c06884d925c77424cb0dfcbf2c4a604d388b9909a4a7f793b9c7f35f22edaa76459c027a764cd677895671e62a83998665522e3fa88eb2050989a519994b01082f515ae7cd2ee0a254fb0198a76bdd2c798d760e796a3be64cfb7eaad57b329b2fbf92133d4ff41044df767bed0074988622ee218bb346933fc67098b54530ab830ace483698b1f5c47e1187b7966b2d9ab56216050d6254ac6d4521294a3fe9fd3b1ae8354fe376d13a437bd5ee23aa2de7dffac5e567b1cbb3d13c860a42af9a77aa8d1b8304db6f6a4c818989919b84f0c49dfadcdbb26bbeb6ac233e0017cb79c725f98a48640d9386cf87119ce961ffb9d8dde2ab722f8f7f7387b12e8af574c29b189d865ab1f63e4eb0b108e529009ab7cb7d7e921c9bc90879112e4b5efc03f021f0097fc7e108e01b0b256d262bc0c8816a023bf33ab221489aa18c67da45ca2f26a7672ae52aeb346c88564c92e0b960f8afc3b4f0a4ff8aa889d222978f0f63848717750e7b1b68368c38be2e07c2ca4ab60209468acb44f90a2ba0328997c3a7a129a83619f8edc4003e5bdbf18295cabdf55c5088d5db20ec6caa20cec7bcaed33165fcd84bae9232bf2862cf0f235bb92caa47609d670157c181c1ec01ad7b1f5a76852f8af9a256f6cdda717ff15191b75639fce887a917442ba8a3c1b70a6b485a95dcce9b403af4c9e2f02739f805c5b520e6b1d972435a10c29499a30ef29e4f82629fd0532103245c9d837728d8ea1f60fadb0b4384f30e4dbefe1844ce4540ae4b000c21bcf7eb6300570d1740e6deb2484455656a174f42fcd9023903b6c1f9f417a427dbb48f767d19d8cdc5bfbba51142f6c033b14bdcad9fe0fb91e992932168292c5ca21ca96934b6e48c7a964b9fec9789a6a2cb2bc60d788045f05493f75e26bb84252c0d3e64b33b311346ba572cc35f23b754df5b7ed1a8e7337a7285d4cc056b4104e7c1f339ff479fe61d9737b3321bf40e48902222548cfe0613557972b75e3dbf90062fdc7b0f495c86959a55e9cb9c3bec5d8795287fc178cc501e465800a0337bdc0798dfeb88d1cca5f3788ab66045286b1f29462aa59222c6230cc7075009e05cb806e1ec161cd15a7ec7cb4542660c69e5f0e144401905143773352b046afae7d07a59746e52338b87ad918a586c3d84e7e7e3529df23ea3a39a6074388235323d695497349b64081f29b18eead3cec4c7471b90fdde7c32265abb81e79f44cb9775f5741c381a0ff7589e7e12a15dd570d5bbe34aeac5cc624a91e97ce007c672d2759c4e7ff7b2f088516fc7e27fce932f3a1c7e55dbf9e9294a242b1501384dbb0524759ee71a08bd072ad3f7bbe429a9084ac1ab366b639d5e42ff1900d609308cbb7491fbbd8910adfc3b596eadf36968f6f97297cfc71894cc36d37711ccae89877c7f08c321d373cdf7b9e7f8c66ba751e219e8daf201533e0b899fe2b28f0f1daf4b6618d8ff940fc55c99ba36cc47e45fdfe119381a6ba365f8eebc5de374219b065783d1620afa93a79da21a29cc8a00ccbb701154217c43a226d9f6e731b928ccbc0b4bf7d036ffc5b0adca3a2ff0ae81a0f7680524612c12e639e5a83ad97c6240b9d17c3b784dbae7485cbf8756d901e699782bb843d5e1172a43d4fae73343e342dc8d1a42a8923e67d91ec503ae929304d9618e5b054261007fe1e99815e4c6442b176431d32c30a1e3799601561a2ff7a42d152264dd3802f9b5845241cf3e2ab11538ae3ce50d92d394abe9645fbf216460bf5b3a18daa4dc033816c40b6cc264eb48cf04929367d012f0d2dc07ec1ddae20ddad5dfc850680220da0709c4c8d6ed022ce733fea0c78ce89dbe0bb7e9aa41fa02f6b6dac067996627f01d108ba2c6f3b02167f83072ae09bfe41cd2427483e5eee21de791afcc26dd748f7ff7df6b6df3a4e79a3c8e57b5f5a654f57d4f16c0f310ba50136094eebf798d60b6afef1c382dffeff27935135ebebfd9d63eff0b6e9cbdda54cdd531cddcf9911dca5bbcda13a6c6ddadbb0e042a95c22b95adf3739af9159e4305bbf8bc90ace1031635dfb884c511f3b83065b16b121e3e73e3a11927c57b489521ad27a33e2c42fbfece50a2a145272522b8737be0052b5d320c327cf66116edcad321dcc75f41537806e3b6aef255ca7f4a154bf002bb752bc756af9651f3d3cfdef526bfe519146cd7f0000007600000000f5f35a3564c15d727f4ad4ceff267788ba0cfe00eec5c9290000001900000000d8a8ca4960e9a5623413dc0721bfd9ab1c14cb51d7abbda00000003900000000d9dbf883e7e9eaaefb1fde950991f22bc5184fc2a5eade680000007100000000fdddaa04f154eb8b313eb9f5a126136cddc625abe9d721b90000005f0000000039b0054fac44ca56ea60137047303b25df851b5ba196b92600000036000000008eba5545f2569e1f386632fcf5721694ed9753ee10909f67000000d100000000a4d30aba0c3e346aa670c918be05d00c8f4c9b0a5e81f9e30000009a000000001d1d011f2b011f2c011f2d011f2e011f2f011f30011f31011f32011f33011f34011f35011f36011f37011f38011f39011f3a011f3b011f09011f1001201501221504285801311201321101330b01340a013e37043e38044235044236044a2e014a2f014a30014a31014b2e014b2f014b30014b3101563a03573502573602573702573802573a095f3a02603533603633603733603833603a09683a01693505693605693705693805693a09723505723605723705723805723a09763501763601763701763801763a08763b03492e7800492f780049307800493178001d18000000e00000000000000000000000001d1c06ffff200000000000000000000000011e18000000dfff20000000000000000000001e1c06ffff2000e0000000000000000000014c2f000000000000000000000001680000034d5606ffffffffffffffffffffff00000001005c01015b01025a01035901045801054001063f01073e01083d01093c010a10010b09010c3b010d3a010e39010f3801103701113601123501133401143301153201163101173001182f01192e011a2d011b2c011c2b011d1901202b01202c01202d01202e01202f01203001203101203201203301203401203501203601203701203801203a01203b012009012010012235042236042237042238043227013426013e57043f57014e1501770908771008005c5c01015b5b01025a5a01035959010458580105404001063f3f01073e3e01083d3d01093c3c010a1010010b0909010c3b3b010d3a3a010e3939010f3838011037370111363601123535011334340114333301153232011631310117303001182f2f01192e2e011a2d2d011b2c2c011c2b2b0121351b0121361b0121371b0121381b01215915012115170122351a0122361a0122371a0122381a0122151601233f0901233f10012340090123401001243f10012440100224521004253f09012540090225520904265808012609140126101401275807012709130127101301293e10012a3e10012b4210012c4209012d4110012e4109012f2909012f2910012f3c09012f3c10012f0309012f031001302809013028100130020901300210013227100134260901353a4401353a4801353a4c01353a5001353b4401353b4701353b4a01353b5101363a4201363a4601363a4a01363a4e01363b4201363b4901363b4c01363b4f013739140138391301393714013a3553013a3653013a3853013a3914013b3552013b3652013b3743013b3852013b3913013c3540013c3640013c4057013d2935013d2936013d2957013d353e013d3517013d363e013d3603013d373e013d3717013d383e013d3817013e2835013e2836013e2857013e3516013e3602013e3716013e3816013f384301403544014036440140374401403844014129370141353c014135170141363c014136170141373c01413753014137080141383c0141385301413808014228370142351601423616014237520142370701423852014238070143321401443213014532060146320501473208014832070149292b0149292d01492b3d01492b0301492b0801492c3d01492c0801492c1401492d3d01492d1701492e3d01492e5301492f3d01492f530149303d014930530149313d014931530149343d0149343e01493403014934080149340f014a282b014a282d014a2b02014a2b07014a2c07014a2c13014a2d16014a2e52014a2f52014a3052014a3152014a3402014a3407014a340e014c2e02014c2e07014c2f02014c3013014c3113014d0207014e1515014f3a5101503a5001513a4f01513b5101523a4e01523b5001532a3a01533b4f0154283a0154351a0154361a0154371a0154381a01543a4101543b4e0155354001553640015537400155384001553b410156354801563648015637480156384801572a3b01583a4d01593a4c015a3a4b015a3b4d015b3a4a015b3b4c015c2a3a015c3b4b015d283a015d3a41015d3b4a015e3543015e3643015e3743015e3843015e3a53015e3b41015e3b55015f2a35105f2a36105f2a37105f2a38105f353d045f3541085f3542025f3545015f363d045f3641085f3642025f3645015f373d045f3741085f3742025f3745015f383d045f3841085f3842025f3845015f3b5301602a3b01613a4901623a4801633a4701633b4901643a4601643b4801652a3a01653b470166283a01663a4101663b460167293b016735450167364501673745016738450168354401683644016837440168384401692a3b016a3a45016b3a44016c3a43016c3b45016d3a42016d3b44016e2a3a016e3b43016f283a016f3a41016f3b420170283b0170354201703642017037420170384201703a5201703b540171350301713603017137030171380301713b5201722a3b01733a41017314580174354101743641017437410174384101743b41017413580175293b017535520175355301753652017536530175375201753753017538520175385301753a540175415801761558227709420177104201353a450100353a490100353a4d0100353a510100353b450100353b480100353b4b0100353b4e0100363a430100363a470100363a4b0100363a4f0100363b430100363b460100363b4d0100363b500100223559000100002236590001000022375900010000223859000100004c2e03000100004c2e08000100004c2f03000100004c3014000100004c3114000100004d0208000100004d0307000100007542580001000077093e0001000077103e000100001e181806ffffffffe4000000000000000000011e181c000000000038000000000000000000001e1c1c06ffffffffe4000000000000000000014c2e4006fffffffffffffffffffffe1ffffffd4c2f4006fffffffffffffffffffffe1ffffffd4d303e06ffffffffffffff87ffffff000000014d303f06ffffffffffffff0ffffffe000000014d304006fffffffffffffe1ffffffc000000014d304206ffffffffffffffffff87ffffff00014d313e06ffffffffffffff87ffffff000000014d313f06ffffffffffffff0ffffffe000000014d314006fffffffffffffe1ffffffc000000014d314206ffffffffffffffffff87ffffff00014d310e000000000000000000000001000000004d310f000000000000000000010000000000004d030800000000000000000000000100000000553a5300070000000000000000000000000000553a0306f90000000000000000000000000001553b5500070000000000000000000000000000553b0806f90000000000000000000000000001563b5300070000000000000000000000000000563b0306f90000000000000000000000000001673a5200070000000000000000000000000000673a0206f90000000000000000000000000001673b5400070000000000000000000000000000673b0706f90000000000000000000000000001683b5200070000000000000000000000000000683b0206f90000000000000000000000000001743a5400070000000000000000000000000000743a0706f900000000000000000000000000011f2b15011f2c15011f2d15011f2e15011f2f15011f3015011f3115011f3215011f3315011f3415011f3515011f3615011f3715011f3815011f3915011f3a15011f3b15011f0915011f101501213559012135170121365901213617012137590121371701213859012138170121151b012235160122361601223716012238160122151a012410110125090a01265814012608090126081001275813012707090127071001283e09012b1012012c090b012d1011012e090a012f090b012f10120130090a0130101101311012013210110133090b0134090a01353a1401353b1401363a1301363b13013a3514013a3614013a3814013a3953013b3513013b3613013b3713013b3813013b3952013d351b013d361b013d371b013d381b013e3548013e3648013e3748013e38480140293701403508014036080140370801403808014135530141365301413703014138030142355201423652014237020142380201492b1401492c0301492d1401492e1401492f14014930140149311401493414014a2b13014a2c02014a2d13014a2e13014a2f13014a3013014a3113014a3413014b2e3c014b2f3c014b303c014b313c014c2e13014c2f07014c2f13014c3056014c315601225915000100002f3d09000100002f3d1000010000303c0900010000303c10000100003d353f000100003d363f000100003d373f000100003d383f000100003e353e000100003e363e000100003e373e000100003e383e0001000041353d0001000041363d0001000041373d0001000041383d0001000042353c0001000042363c0001000042373c0001000042383c00010000492b3c00010000492c3c00010000492d3c00010000492e3c00010000492f3c0001000049303c0001000049313c0001000049343c0001000049343f000100004a2b3d000100004a2c3d000100004a2d3d000100004a2e3d000100004a2f3d000100004a303d000100004a313d000100004a343d000100004a343e000100004c2e3e780000014c2e3ff00000024c2e14000100004c2f3e780000014c2f3ff00000024c2f08000100004c2f14000100004d3041780000014d314178000001");
        assembly ("memory-safe") {
            return(add(code, 32), mload(code))
        }
    }
}
