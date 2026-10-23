// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.36;

/// The registry every successfully verified statement is reported to (one call per proof).
interface IVerificationRegistry {
    /// `publicInput`     = final registers x10..x17 (a0..a7), each u32 LE, concatenated;
    /// `auxInput`        = final registers x18..x25 (s2..s9), same encoding;
    /// `setupCommitment` = keccak256 of the setup oracle's Merkle cap (CAP digests, BE u32 words)
    ///                     — the circuit setup (lookup tables) the proof was verified against.
    function markVerified(bytes32 publicInput, bytes32 auxInput, bytes32 setupCommitment) external;
}

contract GkrWhirVerifier {
    // ── Registry (set once at construction, never zero) ─────────────────────
    address public immutable registry;
    constructor(address registry_) {
        require(registry_ != address(0), "registry is zero");
        require(registry_.code.length > 0, "registry has no code");
        registry = registry_;
    }
    // Every `__TEMPLATE_*` constant below is assigned by the generator (assemble.rs); in the
    // template they hold the string literal "{unassigned}", which does not compile as a number —
    // a generator that forgets one cannot produce a buildable verifier. Inline assembly can only
    // consume literal (numeric-expression) constants, so the literal lives in the declaration.

    // ── Generic (used throughout) ───────────────────────────────────────────
    uint256 constant MINIMUM_FREE_HEAP_PTR = 2048; // via_ir memoryguard reservation is 0x4c0 = 1216 today (guarded below)
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
    // the first two slots of the safe region; the generated heap (below) starts 64 bytes
    // higher. INVARIANT (Yul forbids constant arithmetic in assembly, so these are spelled as
    // literals): P_PTR == MINIMUM_FREE_HEAP_PTR, CIRCUIT_PTR == MINIMUM_FREE_HEAP_PTR + 32, and
    // the generator starts the heap at MINIMUM_FREE_HEAP_PTR + 64 (it reads the constant).
    uint256 constant P_PTR  = 2048;      // == MINIMUM_FREE_HEAP_PTR  (spill-safe slot 0)
    // Fixed heap slot holding the circuit-layer calldata cursor, so gate/cache sub-functions
    // read it via mload instead of a `ptr` parameter (that param was the single deepest stack
    // slot pushing each of them 1 over the EVM limit). Spill-safe slot 1, just above P_PTR.
    uint256 constant CIRCUIT_PTR = 2080; // == MINIMUM_FREE_HEAP_PTR + 32
    uint256 constant ROUNDS = 200; // test-harness only (GKRStreamGen); stripped from production

    // ── Heap layout (GENERATED sizes: the regions are chained back to back from
    //    MINIMUM_FREE_HEAP_PTR + 64 by the `*_PTR()` accessors below, each region's size — a
    //    whole number of 32-byte words — derived from the circuit / prover config, see
    //    gkr_heap_regions in assemble.rs). NOTE: the accessors are deliberately a chain of
    //    `add(previous(), SIZE)` calls rather than absolute literals — with absolute literals the
    //    IR optimizer emits ~1.7 KB more bytecode for the layer-0 gates (measured; literal
    //    LOGUP_CHALLS_PTR alone triggers it). The WHIR half's regions follow at the chain's
    //    end (its generated absolute offsets; the fallback's first statement asserts, at
    //    compile time, that the chain ends exactly where the WHIR map starts).
    // HEAP ORDER: memory challenges (7), logup challenges (2), point (rounds), gas probes (2),
    // seed + transcript scratch (the preimage copy / cache array / SEED±96 absorb scratch),
    // batching (1), dim-reduce claims (NUM_OUTPUTS), eq (max(OUTPUT_EVALS, NUM_OUTPUTS)),
    // absorb scratch (32 + max absorb), permutation products (4), circuit claims (widest layer),
    // layer-0 gate values (gate slots), layer-0 packed term table.
    uint256 constant __TEMPLATE_GKR_MEMORY_CHALLS_BYTES  = 32 * 7;
    uint256 constant __TEMPLATE_GKR_LOGUP_CHALLS_BYTES   = 32 * 2;
    uint256 constant __TEMPLATE_GKR_POINT_BYTES          = 32 * 21;
    uint256 constant __TEMPLATE_GKR_INIT_GAS_BYTES       = 32;
    uint256 constant __TEMPLATE_GKR_MAIN_GAS_BYTES       = 32;
    uint256 constant __TEMPLATE_GKR_SEED_BYTES           = 32 * 29;
    uint256 constant __TEMPLATE_GKR_BATCHING_BYTES       = 32;
    uint256 constant __TEMPLATE_GKR_CLAIMS_BYTES         = 32 * 10;
    uint256 constant __TEMPLATE_GKR_EQ_BYTES             = 32 * 10;
    uint256 constant __TEMPLATE_GKR_ABS_BYTES            = 32 * 64;
    uint256 constant __TEMPLATE_GKR_PERM_PROD_BYTES      = 32 * 4;
    uint256 constant __TEMPLATE_GKR_CIRCUIT_CLAIMS_BYTES = 32 * 74;
    uint256 constant __TEMPLATE_GKR_GATEVAL_BYTES        = 32 * 120;
    uint256 constant __TEMPLATE_GKR_QTABLE_BYTES         = 32 * 105;
    uint256 constant __TEMPLATE_GKR_F1_V0_BYTES          = 32 * 986; // F1: the decoded v0 GKR calldata image

    // ── Transcript preimage: registers ‖ final_pc/ts ‖ inits/teardowns top_bits ‖ setup_cap ‖
    //    memory_cap (LE u32 words). The register prefix is the RISC-V machine state (fixed);
    //    the tail offsets depend on the circuit (teardown sets) and config (cap) → generated. ──
    uint256 constant NUM_REGISTERS              = 32;
    uint256 constant PREIMAGE_REGISTER_STRIDE   = 12; // (value, ts_low, ts_high) as LE u32
    uint256 constant PUBLIC_INPUT_FIRST_REGISTER = 10; // x10..x17 (a0..a7)
    uint256 constant AUX_INPUT_FIRST_REGISTER    = 18; // x18..x25 (s2..s9)
    uint256 constant MARK_WORD_REGISTERS         = 8;  // 8 u32 values = one bytes32
    uint256 constant __TEMPLATE_PREIMAGE_FINAL_PC_OFFSET   = 32 * 12; // = NUM_REGISTERS * PREIMAGE_REGISTER_STRIDE
    uint256 constant __TEMPLATE_PREIMAGE_TOP_BITS_OFFSET   = 32 * 12 + 12; // final_pc + 12
    uint256 constant __TEMPLATE_PREIMAGE_SETUP_CAP_OFFSET  = 32 * 12 + 12 + 2 * 4; // top_bits + num_teardown_sets * 4
    uint256 constant __TEMPLATE_PREIMAGE_MEMORY_CAP_OFFSET = 32 * 12 + 12 + 2 * 4 + 8 * 32; // setup_cap + CAP * 32
    uint256 constant __TEMPLATE_GKR_INIT_PREIMAGE_BYTES    = 32 * 12 + 12 + 2 * 4 + 8 * 32 + 8 * 32; // memory_cap + CAP * 32
    // The inits/teardowns RAM-set base chunk indices (`top_bits`) are deployment parameters of
    // the program: the prover's preimage values must EQUAL these (checked in transcript_init),
    // and the layer-0 inits/teardowns gates use the constants. One uint8 per teardown set.
    uint8 constant __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_0 = 0;
    uint8 constant __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_1 = 1;
    uint256 constant __TEMPLATE_EXTERNAL_POW_BITS = 20; // external-challenge PoW difficulty
    uint256 constant __TEMPLATE_EXPECTED_FINAL_PC = 262645; // program's terminal PC — binds the verified statement to this program

    // ── GKR entry + dimension reduction (generated from the circuit / config) ─────────────────
    uint256 constant __TEMPLATE_GKR_NUM_OUTPUTS        = 5 * 2; // GKR output polys (global_output_map lines)
    uint256 constant __TEMPLATE_GKR_OUTPUT_LOG2        = 2; // log2 of the explicit output layer (sumcheck_explicit_output_size_log_2)
    uint256 constant __TEMPLATE_GKR_OUTPUT_EVALS       = 1 << 2; // 2^OUTPUT_LOG2 evals per output poly
    uint256 constant __TEMPLATE_GKR_INIT_BYTES         = 10 * 4 * 16; // NUM_OUTPUTS * OUTPUT_EVALS * 16 (one u128 per eval)
    uint256 constant __TEMPLATE_GKR_LSB_LINES_BYTES    = 10 * 32; // NUM_OUTPUTS * 32 (one [E;2] line per output)
    uint256 constant __TEMPLATE_GKR_DIM_REDUCE_LAYERS  = 21 - 2; // trace_log2 - OUTPUT_LOG2
    uint256 constant __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS = 21; // trace_log2

    // ── GKR→WHIR handoff (generated; shared with the WHIR half where the names coincide) ──────
    uint256 constant __TEMPLATE_WHIR_CAP            = 1 << 3; // base-oracle merkle cap size
    uint256 constant __TEMPLATE_WHIR_BATCH_POW_BITS = 13; // batched_proximity_check_pow_bits
    // Base-layer at-point claims (dense in layer0's calldata eval block): mem++wit = NUM_MEMWIT
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
    // Must match the prover's `eval_leaves` cargo feature. 0 (default): intermediate
    // oracles commit multilinear-COEFFICIENT leaves -> fold with the plain monomial
    // tensor (fold_multilinear). 1 (eval_leaves): they commit raw EVALUATIONS -> fold
    // with the coset base-root (fold_coset), like the round-0 base oracle.
    uint256 constant W_EVAL_LEAVES = 0;

    // ── Generated from the prover config + circuit (`__TEMPLATE_WHIR_*`) ─────────────────────
    // Every value below is assigned by the generator (the "{unassigned}" placeholder does not
    // compile, so a forgotten assignment is caught); the Yul only ever references the names
    // (inline assembly needs literal constants, so the literal lives in the declaration alone).
    // RS-codeword evaluation-domain generator and its inverse — a primitive 2^codeword_log2-th
    // root of unity (`Proth120::TWO_ADICITY_GENERATORS[codeword_log2]`).
    uint256 constant __TEMPLATE_WHIR_GEN     = 0x0293B319B108C8A856BF8B8AB7799ECD;
    uint256 constant __TEMPLATE_WHIR_GEN_INV = 0x0290A0CB0CAD8AC9DAFCDC73EBD1A223;
    uint256 constant __TEMPLATE_WHIR_NUM_ROUNDS   = 5;
    uint256 constant __TEMPLATE_WHIR_NZ           = 21 + 3;  // WHIR eval-point coords = trace_log2 + pack_log2
    uint256 constant __TEMPLATE_WHIR_GCOUNT       = ((96 + 8 - 1) >> 3) + ((10 + 8 - 1) >> 3) + 1;  // gamma-batched base columns + 1
    uint256 constant __TEMPLATE_WHIR_RFIN         = 24 - (1 + 4 + 4 + 4 + 4);  // final-poly log2 = message_log2 - sum(folds)
    // Merkle cap: each commitment is a cap of 2^CAP_LOG2 hashes, so a Merkle path is CAP_LOG2
    // levels shorter. Caps shrink paths but grow every commitment to CAP*32 bytes.
    uint256 constant __TEMPLATE_WHIR_CAP_LOG2 = 3;
    // Merkle leaf/node hash: keccak256 truncated to the digest bytes (the high bytes kept).
    uint256 constant __TEMPLATE_DIGEST_MASK = 0xffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000;
    uint256 constant __TEMPLATE_F1_DIGEST_BYTES = 25; // Merkle digest bytes on the F1 wire
    // The setup data contract: STOP ‖ setup frontier (if any) ‖ pinned setup cap image ‖ GKR
    // term table; its code hash is checked once per call, before any read.
    address constant __TEMPLATE_F1_FRONTIER = 0x5FbDB2315678afecb367f032d93F642f64180aa3;
    uint256 constant __TEMPLATE_F1_FRONTIER_HASH = 0x3add74f56c38536749fbc90f72780bd692f9f1eff092aff241ea5ba37990bcc6;
    uint256 constant __TEMPLATE_F1_DATA_CAP_OFFSET = 12801;
    uint256 constant __TEMPLATE_F1_DATA_QTABLE_OFFSET = 13057;
    // Setup frontier: the setup tree's 2^LEVEL nodes at that level (DIGEST_BYTES each, physical
    // order) after the STOP byte; setup paths stop SKIP = LEVEL − CAP_LOG2 levels early.
    uint256 constant __TEMPLATE_F1_FRONTIER_LEVEL = 9;
    uint256 constant __TEMPLATE_F1_FRONTIER_SKIP = 6;

    // ── Memory map (generated: contiguous regions above the GKR heap, each sized from the
    //    schedule — see WhirGenConfig::memory_regions for every region's size formula) ────────
    uint256 constant __TEMPLATE_WHIR_SEED_PTR     = 48032;  // seed + in-place absorb scratch
    uint256 constant __TEMPLATE_WHIR_Z_PTR        = 48320;  // z: nz coords
    uint256 constant __TEMPLATE_WHIR_POW_PTR      = 49088;  // (scalar, running eq, coefficient) x numpow
    uint256 constant __TEMPLATE_WHIR_ACC_PREF_PTR = 52928;
    uint256 constant __TEMPLATE_WHIR_GAMMA_PTR    = 52960;  // gcount gamma powers
    uint256 constant __TEMPLATE_WHIR_FOLD_CH_PTR  = 53440;  // max_fold challenges
    uint256 constant __TEMPLATE_WHIR_HPO_PTR      = 53568;  // 2^(max_fold-1) high-power offsets
    uint256 constant __TEMPLATE_WHIR_FBUF_PTR     = 53824;  // 2^max_fold folding buffer
    uint256 constant __TEMPLATE_WHIR_LEAF_PTR     = 54336;  // leaf hashing scratch
    uint256 constant __TEMPLATE_WHIR_REG_CD       = 54784;  // calldata cursor
    uint256 constant __TEMPLATE_WHIR_REG_CLAIM    = 54816;
    uint256 constant __TEMPLATE_WHIR_REG_NUMPOW   = 54848;
    uint256 constant __TEMPLATE_WHIR_REG_ZIOFF    = 54880;
    uint256 constant __TEMPLATE_WHIR_REG_CC       = 54912;
    uint256 constant __TEMPLATE_WHIR_REG_CURDELIN = 54944;
    // GKR→WHIR handoff: the WHIR batching challenge, written by the GKR half's emit_gkr_mark.
    uint256 constant __TEMPLATE_WHIR_HANDOFF_BATCHING_PTR = 54976;
    // cap regions (CAP*32 bytes each)
    uint256 constant __TEMPLATE_WHIR_BCAP0_PTR    = 55008;  // witness base-oracle cap
    uint256 constant __TEMPLATE_WHIR_BCAP1_PTR    = 55264;  // setup base-oracle cap
    uint256 constant __TEMPLATE_WHIR_QCAP_PTR     = 55520;  // current query cap (rounds >= 1)
    uint256 constant __TEMPLATE_WHIR_NCAP_PTR     = 55776;  // just-read intermediate cap
    // Per-round query drawing (matches prover `draw_query_bits`/`BitSource`):
    //   QIDX_BUF holds the drawn query indices (max_q words);
    //   DRAW_BUF holds the little-endian u32 words squeezed from the seed (one per slot).
    uint256 constant __TEMPLATE_WHIR_QIDX_BUF_PTR = 56032;
    uint256 constant __TEMPLATE_WHIR_DRAW_BUF_PTR = 56416;
    // do_final scratch: the plain-text tail is 2^RFIN monomials (MONO), then the tail absorb +
    // halving-fold scratch (FEVAL, 32 + 2^RFIN words).
    uint256 constant __TEMPLATE_WHIR_MONO_PTR     = 56928;
    uint256 constant __TEMPLATE_WHIR_FEVAL_PTR    = 61024;

    fallback(bytes calldata) external returns (bytes memory) {
        // The verified statement, read out of the MARK region once the assembly block has
        // finished and reported through the typed registry interface below (the compiler does
        // the ABI encoding of both the call and the return data).
        bytes32 publicInput;
        bytes32 auxInput;
        bytes32 setupCommitment;
        // NOTE: "memory-safe" is TRANSIENT — it lets solc spill the 1 leftover stack slot in the
        // OLD sumcheck_compress_2pass (dim-reducing, pending replacement by the validated
        // GkrDimReduce logic). The hand-placed memory is disjoint from spill slots, but
        // re-audit memory-safety once the dim-reducing port lands.
        assembly ("memory-safe") {
        mstore(P_PTR, 0x7000000000000000000000000000001)
        // Layout self-check (constant-folded away when it holds): the GKR region chain must end
        // exactly where the generator placed the WHIR half's first region.
        if iszero(eq(add(F1_V0_PTR(), __TEMPLATE_GKR_F1_V0_BYTES), __TEMPLATE_WHIR_SEED_PTR)) {
            revert(0, 0)
        }
        // the setup data contract is this deployment's data: check its code before any read
        if iszero(eq(extcodehash(__TEMPLATE_F1_FRONTIER), __TEMPLATE_F1_FRONTIER_HASH)) { revert(0, 0) }
        // assembly ("memory-safe") {
        // Proof/transcript bytes preserve logical stream order. Rust must append
        // fixed-width BE integer bytes: u32::to_be_bytes(), u64::to_be_bytes(),
        // u128::to_be_bytes(). 32-byte hashes/caps/roots are absorbed as raw bytes.
        // For u128 pairs calldata is [x0:16][x1:16], so x0 is shr(128, word)
        // and x1 is and(word, MASK). Smaller lanes follow the same BE packing rule
        // with larger shifts. Hash challenges use the earlier 16 hash bytes
        // first: shr(128, seed), then and(seed, MASK).

        // Heap regions, chained by their GENERATED sizes (the generated circuit.yul calls these
        // by name). The chain order here is verified by the generator against its allocator.
        // +64: the first two safe slots hold P_PTR and CIRCUIT_PTR (see the layout note).
        function MEMORY_CHALLS_PTR() -> ptr { ptr := add(MINIMUM_FREE_HEAP_PTR, 64) }
        function LOGUP_CHALLS_PTR()  -> ptr { ptr := add(MEMORY_CHALLS_PTR(), __TEMPLATE_GKR_MEMORY_CHALLS_BYTES) }
        function POINT_PTR()         -> ptr { ptr := add(LOGUP_CHALLS_PTR(), __TEMPLATE_GKR_LOGUP_CHALLS_BYTES) }
        function GKR_INIT_GAS_PTR()  -> ptr { ptr := add(POINT_PTR(), __TEMPLATE_GKR_POINT_BYTES) }
        function GKR_MAIN_GAS_PTR()  -> ptr { ptr := add(GKR_INIT_GAS_PTR(), __TEMPLATE_GKR_INIT_GAS_BYTES) }
        // The seed region also holds the transcript scratch the absorbs use at SEED+32/+64, the
        // preimage copy (transcript_init) and the per-layer cache array (circuit.yul); the
        // generator sizes it for the largest of those.
        function SEED_PTR()          -> ptr { ptr := add(GKR_MAIN_GAS_PTR(), __TEMPLATE_GKR_MAIN_GAS_BYTES) }
        function GKR_INIT_SCRATCH_PTR()   -> ptr { ptr := add(SEED_PTR(), mul(32, 1)) }
        function GKR_INIT_CLAIM_PTR()     -> ptr { ptr := add(SEED_PTR(), mul(32, 2)) }
        function GKR_CIRCUIT_ALPHA2_PTR() -> ptr { ptr := add(SEED_PTR(), mul(32, 1)) }
        function GKR_CIRCUIT_CACHE_PTR()  -> ptr { ptr := add(SEED_PTR(), mul(32, 2)) }
        // Dim-reducing / entry regions (used before the circuit layers).
        function GKR_BATCHING_PTR() -> ptr { ptr := add(SEED_PTR(), __TEMPLATE_GKR_SEED_BYTES) }                 // running batching
        function GKR_CLAIMS_PTR()   -> ptr { ptr := add(GKR_BATCHING_PTR(), __TEMPLATE_GKR_BATCHING_BYTES) }     // NUM_OUTPUTS dim-reduce claims
        function GKR_EQ_PTR()       -> ptr { ptr := add(GKR_CLAIMS_PTR(), __TEMPLATE_GKR_CLAIMS_BYTES) }         // eq[OUTPUT_EVALS] / SI[NUM_OUTPUTS]
        function GKR_ABS_PTR()      -> ptr { ptr := add(GKR_EQ_PTR(), __TEMPLATE_GKR_EQ_BYTES) }                 // absorb scratch (32 + max absorb)
        // Permutation-identity products: read_poly, write_poly, teardown_poly, init_poly
        // (∏ of each relevant GKR output poly's OUTPUT_EVALS elements). Filled in gkr_init,
        // consumed by check_permutation_identity; untouched by compress/circuit.
        function GKR_PERM_PROD_PTR() -> ptr { ptr := add(GKR_ABS_PTR(), __TEMPLATE_GKR_ABS_BYTES) }
        // Circuit-layer claims array: the previous circuit layer's at-point evals,
        // offset-indexed, that this layer's `compute_claim` batches into its initial claim.
        // Threaded across layers: each layer writes its input evals here for the next one.
        // Sized by the generator for the widest layer.
        function GKR_CIRCUIT_CLAIMS_PTR() -> ptr { ptr := add(GKR_PERM_PROD_PTR(), __TEMPLATE_GKR_PERM_PROD_BYTES) }

        // Layer-0 table-driven quadratic-gate evaluation (size opt). GATEVAL holds one reduced
        // value per quadratic gate (filled by the compact bucket loops from GKR_QTABLE, read by
        // the Horner chunk functions as `mload(GATEVAL+32*slot)`). QTABLE is the packed record
        // stream (slot,a,b,coeff) written via mstore immediates. Both live in pristine (zero,
        // never-written) heap above every region written before layer 0, so GATEVAL needs no
        // zeroing. Only used during layer 0's point-check; nothing else touches these slots.
        function GKR_GATEVAL_PTR() -> ptr { ptr := add(GKR_CIRCUIT_CLAIMS_PTR(), __TEMPLATE_GKR_CIRCUIT_CLAIMS_BYTES) }
        function GKR_QTABLE_PTR()  -> ptr { ptr := add(GKR_GATEVAL_PTR(), __TEMPLATE_GKR_GATEVAL_BYTES) }
        // F1: the v0 GKR calldata image, written once by f1_decode; the verifier reads it at v0 offsets.
        function F1_V0_PTR()       -> ptr { ptr := add(GKR_QTABLE_PTR(), __TEMPLATE_GKR_QTABLE_BYTES) }

        // ── F1 decoder: the GKR half's only calldata reader. Writes the v0 GKR calldata image
        // at F1_V0_PTR(); the GKR half reads that image at v0 offsets, the WHIR half reads its
        // stream from calldata after the GKR section.
        // FE-run(n) at cd: element j = bits [123j, 123j + 123) MSB-first, the pad bits of the last
        // byte zero. Elements 2i, 2i + 1 lie in the word loaded at byte bit >> 3 (bit & 7 ≤ 7,
        // 7 + 246 ≤ 256) and go to the two BE16 lanes at dst + 32i. No range check here: the
        // verifier checks every lane of these runs < P where it reads it (output evaluations, LSB
        // lines, at-point evaluations).
        function f1_lanes(x) -> w {
            w := or(shl(128, and(shr(123, x), 0x7ffffffffffffffffffffffffffffff)), and(x, 0x7ffffffffffffffffffffffffffffff))
        }
        function f1_run(cd, n, dst) {
            // four pairs = 984 bits = 123 bytes: pair k at byte (246k) >> 3, shifted by 10 − (246k & 7)
            for { let end := add(cd, mul(123, shr(3, n))) } lt(cd, end) { cd := add(cd, 123) } {
                mstore(dst, f1_lanes(shr(10, calldataload(cd))))
                mstore(add(dst, 32), f1_lanes(shr(4, calldataload(add(cd, 30)))))
                mstore(add(dst, 64), f1_lanes(shr(6, calldataload(add(cd, 61)))))
                mstore(add(dst, 96), f1_lanes(shr(8, calldataload(add(cd, 92)))))
                dst := add(dst, 128)
            }
            let bit := 0
            for { let end := mul(246, and(shr(1, n), 3)) } lt(bit, end) { bit := add(bit, 246) } {
                mstore(dst, f1_lanes(shr(sub(10, and(bit, 7)), calldataload(add(cd, shr(3, bit))))))
                dst := add(dst, 32)
            }
            if and(n, 1) {
                mstore(dst, shl(128, and(shr(sub(133, and(bit, 7)), calldataload(add(cd, shr(3, bit)))), 0x7ffffffffffffffffffffffffffffff)))
                bit := add(bit, 123)
            }
            f1_pad(cd, bit)
        }
        // The pad bits after `bits` run bits at cd must be zero.
        function f1_pad(cd, bits) {
            let pad := and(sub(0, bits), 7)
            if and(byte(0, calldataload(add(cd, shr(3, sub(add(bits, pad), 1))))), sub(shl(pad, 1), 1)) { revert(0, 0) }
        }
        // f1_run over the run at (cd, v0): the next F1 and v0 offsets.
        function f1_seq(cd, v0, n) -> next_cd, next_v0 {
            f1_run(cd, n, add(F1_V0_PTR(), v0))
            next_cd := add(cd, shr(3, add(mul(123, n), 7)))
            next_v0 := add(v0, shl(4, n))
        }
        // E1 run of k (b, c) pairs: the round functions read the pairs from calldata (f1_cd) and
        // range-check them; the image slot of round 0 holds the run's bit offset.
        function f1_rounds(cd, v0, k) -> next_cd, next_v0 {
            mstore(add(F1_V0_PTR(), v0), shl(3, cd))
            let bits := mul(246, k)
            f1_pad(cd, bits)
            next_cd := add(cd, shr(3, add(bits, 7)))
            next_v0 := add(v0, shl(6, k))
        }
        function f1_cd(off) -> w {
            w := calldataload(off)
        }
        // A 19-bit limb as the 4 little-endian bytes of its u32, left-aligned.
        function f1_le19(x) -> w {
            w := or(or(shl(248, and(x, 0xff)), shl(240, and(shr(8, x), 0xff))), shl(232, shr(16, x)))
        }
        // TS-run pair i: bits [38i, 38i + 38) = low19 ‖ high19.
        function f1_ts(i) -> lo, hi {
            let bit := mul(38, i)
            let x := and(shr(sub(218, and(bit, 7)), calldataload(add(128, shr(3, bit)))), 0x3fffffffff)
            lo := shr(19, x)
            hi := and(x, 0x7ffff)
        }
        // Byte-reverse each u32 lane of a 32-byte word (BE digest words → preimage LE words).
        function f1_bswap32x8(w) -> r {
            r := or(shr(8, and(w, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00)),
                    shl(8, and(w, 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff)))
            r := or(shr(16, and(r, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000)),
                    shl(16, and(r, 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff)))
        }
        function f1_decode() {
            // preimage: registers (value, ts_low, ts_high) as LE u32
            for { let i := 0 } lt(i, 32) { i := add(i, 1) } {
                let dst := add(F1_V0_PTR(), mul(12, i))
                calldatacopy(dst, mul(4, i), 4)
                let lo, hi := f1_ts(i)
                mstore(add(dst, 4), f1_le19(lo))
                mstore(add(dst, 8), f1_le19(hi))
            }
            {
                let lo, hi := f1_ts(32)
                mstore(add(F1_V0_PTR(), 384), shl(224, 0xf5010400)) // pinned final PC
                mstore(add(F1_V0_PTR(), 388), f1_le19(lo))
                mstore(add(F1_V0_PTR(), 392), f1_le19(hi))
            }
            if and(byte(0, calldataload(284)), 0x3) { revert(0, 0) }
            calldatacopy(add(F1_V0_PTR(), 396), 285, 8)
            // pinned setup cap
            extcodecopy(__TEMPLATE_F1_FRONTIER, add(F1_V0_PTR(), 404), __TEMPLATE_F1_DATA_CAP_OFFSET, 256)
            // memory cap: 8 DIGESTs of 25 bytes
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                let w := calldataload(add(293, mul(25, i)))
                mstore(add(F1_V0_PTR(), add(660, mul(32, i))), f1_bswap32x8(and(w, not(sub(shl(56, 1), 1)))))
            }
            let cd := 493
            let v0 := 916
            calldatacopy(add(F1_V0_PTR(), v0), cd, 8) // external PoW nonce
            cd, v0 := f1_seq(add(cd, 8), add(v0, 8), 40)
            for { let k := 2 } lt(k, 21) { k := add(k, 1) } {
                cd, v0 := f1_rounds(cd, v0, k)
                cd, v0 := f1_seq(cd, v0, 20)
            }
            // circuit layers, top first; at-point eval counts 16 bits each
            for { let l := 0 } lt(l, 5) { l := add(l, 1) } {
                cd, v0 := f1_rounds(cd, v0, 21)
                cd, v0 := f1_seq(cd, v0, and(shr(mul(16, l), 0x006a004a001a0012000c), 0xffff))
            }
            calldatacopy(add(F1_V0_PTR(), v0), cd, 8) // WHIR batching PoW nonce
            if iszero(and(eq(add(cd, 8), 20270), eq(add(v0, 8), 31524))) { revert(0, 0) }
        }

        // Read one little-endian u32 from the transcript preimage (absolute calldata byteoff).
        function preimage_u32(byteoff) -> v {
            let w := mload(add(F1_V0_PTR(), byteoff))
            v := add(add(byte(0, w), shl(8, byte(1, w))), add(shl(16, byte(2, w)), shl(24, byte(3, w))))
        }

        function transcript_4to1_dual(w0, w1, modulus) -> r {
            // Absorb the four coefficients before drawing the round challenge:
            // seed = keccak(seed || w0 || w1), then seed = keccak(seed), r = top128 mod P.
            // F1Oracle.t.sol compares these transcript observations with the v0 path.
            // F1/E1 rebuilds c0..c3 from (b, c) with lanes up to 2P: canonicalize the 4 lanes (mod
            // P) before absorbing, so the transcript binds to the reduced values. Re-pack keeps
            // the [hi|lo] layout.
            mstore(add(SEED_PTR(), 32), or(shl(128, mod(shr(128, w0), modulus)), mod(and(w0, MASK), modulus)))
            mstore(add(SEED_PTR(), 64), or(shl(128, mod(shr(128, w1), modulus)), mod(and(w1, MASK), modulus)))
            let seed := keccak256(SEED_PTR(), 96) // absorb 4 (canonical) coeffs
            mstore(SEED_PTR(), seed)
            seed := keccak256(SEED_PTR(), 32)     // draw
            mstore(SEED_PTR(), seed)
            r := mod(shr(128, seed), modulus)
        }

        function transcript_init(ptr) -> next_ptr {
            // SingleChunk commits the register/PC boundary, top bits and both caps.
            // Hash the LE-u32 preimage, absorb the BE-u64 nonce, check its configured PoW,
            // then draw permutation and lookup challenges. F1Oracle.t.sol checks that
            // both calldata formats produce the same transcript observations.
            mcopy(SEED_PTR(), ptr, __TEMPLATE_GKR_INIT_PREIMAGE_BYTES)
            let seed := keccak256(SEED_PTR(), __TEMPLATE_GKR_INIT_PREIMAGE_BYTES)
            // The inits/teardowns top_bits the prover absorbed must be the program's pinned
            // values (one uint8 constant per RAM set) — the layer-0 inits/teardowns gates are
            // generated against the constants, so a different preimage must not verify.
            if iszero(eq(preimage_u32(__TEMPLATE_PREIMAGE_TOP_BITS_OFFSET), __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_0)) {
            revert(0, 0) }
            if iszero(eq(preimage_u32(add(__TEMPLATE_PREIMAGE_TOP_BITS_OFFSET, 4)), __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_1)) {
            revert(0, 0) }

            // PoW fold: digest = keccak(seed(32) || nonce_be8); require top __TEMPLATE_EXTERNAL_POW_BITS zero.
            let nonce := shr(192, mload(add(ptr, __TEMPLATE_GKR_INIT_PREIMAGE_BYTES))) // 8-byte BE nonce
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

            // SEED_PTR now holds the post-transcript-init seed; the GKR entry (gkr_init) absorbs output evals next.
            next_ptr := add(ptr, add(__TEMPLATE_GKR_INIT_PREIMAGE_BYTES, 8)) // preimage + 8-byte PoW nonce
        }



        // Absorb the explicit output evaluations and draw the evaluation point plus
        // batching challenge. Stream the equality factors while accumulating the
        // NUM_OUTPUTS claims, without retaining a full equality table.
        // claim/alpha remain zero: gkr_compress reads GKR_CLAIMS_PTR / GKR_BATCHING_PTR.
        function gkr_init(ptr) -> next_ptr, claim, alpha {
            let sp := SEED_PTR()
            // absorb output evals: seed = keccak(seed || outputEvals). The INIT_BYTES are bulk-copied
            // raw; canonicity is enforced at the use site below — the claims loop reads every one
            // of these 160 lanes and range-checks `val < P`, so any accepted proof has canonical
            // evals and hence a canonical absorb (cheaper than reduce-on-copy: it reuses the read
            // the claims loop already performs).
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
            // Also accumulate ∏ of the OUTPUT_EVALS elements for the permutation-identity outputs:
            // BTreeMap<OutputType> order => [0]=Perm.read, [1]=Perm.write, [8]=I&T.teardown,
            // [9]=I&T.init (validated in verify_permutation_identity_no_inversion; the generator
            // asserts the artifact's output map has exactly this 5x2 OutputType layout).
            for { let c := 0 } lt(c, __TEMPLATE_GKR_NUM_OUTPUTS) { c := add(c, 1) } {
                let acc := 0
                let prod := 1
                for { let j := 0 } lt(j, __TEMPLATE_GKR_OUTPUT_EVALS) { j := add(j, 1) } {
                    let k := add(mul(c, __TEMPLATE_GKR_OUTPUT_EVALS), j)
                    let val := shr(128, mload(add(ptr, mul(k, 16))))
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
                let pcv := preimage_u32(__TEMPLATE_PREIMAGE_FINAL_PC_OFFSET)
                // Bind the verified statement to this program's terminal PC.
                if iszero(eq(pcv, __TEMPLATE_EXPECTED_FINAL_PC)) {
                revert(0, 0) }
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
                let num_base := add(op, mul(mul(add(2, mul(lk, 2)), __TEMPLATE_GKR_OUTPUT_EVALS), 16)) // col (2+2·lk), eval 0
                let den_base := add(num_base, mul(__TEMPLATE_GKR_OUTPUT_EVALS, 16))                    // col (3+2·lk), eval 0
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

        // One E1 round: (b, c) from the F1 calldata pair at `bit`, a = K − z(b + c), absorb
        // c0..c3 of e_z·(a + bX + cX²) as v0, draw r, K := a + br + cr². t, s, a, c1, c2 stay
        // unreduced where they only feed mulmod or a lane transcript_4to1_dual reduces.
        function f1_e1_round(bit, z, k, modulus) -> r, next_k {
            let x := shr(sub(10, and(bit, 7)), f1_cd(shr(3, bit)))
            let b := and(shr(123, x), 0x7ffffffffffffffffffffffffffffff)
            let c := and(x, 0x7ffffffffffffffffffffffffffffff)
            if iszero(and(lt(b, modulus), lt(c, modulus))) { revert(0, 0) }
            let a := add(k, sub(modulus, mulmod(z, add(b, c), modulus)))
            let t := add(1, sub(modulus, z))
            let s := add(add(z, z), sub(modulus, 1))
            r := transcript_4to1_dual(
                or(shl(128, mulmod(t, a, modulus)), add(mulmod(t, b, modulus), mulmod(s, a, modulus))),
                or(shl(128, add(mulmod(t, c, modulus), mulmod(s, b, modulus))), mulmod(s, c, modulus)),
                modulus)
            next_k := addmod(a, mulmod(r, addmod(b, mulmod(r, c, modulus), modulus), modulus), modulus)
        }
        function sumcheck_rounds(ptr, claim, total_rounds) -> next_ptr, next_claim, eq_scale {
            let modulus := mload(P_PTR)
            eq_scale := 1
            // E1: the round slot holds (b, c) of u = a + bX + cX² with p = e_z·u,
            // e_z(X) = (1 − z) + (2z − 1)X. claim tracks K = u_prev(r_prev); a = K − z(b + c) makes
            // p(0) + p(1) = K, c0..c3 are rebuilt and absorbed as v0, and the returned eq_scale = 1
            // turns the layer's end check into g == K. The (b, c) pairs are read from the F1 calldata
            // run whose bit offset f1_decode left in the first round slot.
            let bit := mload(ptr)
            for { let i := 0 } lt(i, total_rounds) { i := add(i, 1) } {
                let zp := add(POINT_PTR(), mul(i, 32))
                let r
                r, claim := f1_e1_round(bit, mload(zp), claim, modulus)
                bit := add(bit, 246)
                mstore(zp, r)
                ptr := add(ptr, 64)
            }
            next_ptr := ptr
            // Canonicalize: `claim` accumulates as mulmod(...) + c0, i.e. anything in [0, 2P).
            // gkr_dr_final subtracts it from P with wrapping EVM arithmetic, and an unreduced
            // claim would make that check accept a second relation (g·eq_scale ≡ claim − 2^256
            // mod P) — so hand back the residue.
            next_claim := mod(claim, modulus)
        }



        // Dim-reducing final step in its own frame to keep the caller stack shallow.
        // `cp` points at the NUM_OUTPUTS [E;2] LSB lines in sorted order. Compute
        // g (products slots 0,1,8,9; lookup num/den pairs (2,3)(4,5)(6,7); running batching powers;
        // boundary permutation on the last layer), check g*eq_scale==claim, absorb the LSB lines,
        // draw r_last + next_batching, interpolate the next claims (sorted order), grow the point.
        function gkr_dr_final(cp, fs, batching, boundary, eq_scale, claim) -> ncp, nbatch {
            let modulus := mload(P_PTR)
            let SI := GKR_EQ_PTR() // reuse eq scratch as the sorted-index array (NUM_OUTPUTS slots)
            for { let li := 0 } lt(li, __TEMPLATE_GKR_NUM_OUTPUTS) { li := add(li, 1) } {
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
                let word := mload(add(cp, mul(mload(add(SI, mul(step, 32))), 32)))
                g := add(mulmod(gb, mulmod(shr(128, word), and(word, MASK), modulus), modulus), g)
                gb := mulmod(gb, batching, modulus)
            }
            for { let pr := 0 } lt(pr, 3) { pr := add(pr, 1) } {
                let wN := mload(add(cp, mul(mload(add(SI, mul(add(2, mul(pr, 2)), 32))), 32)))
                let wD := mload(add(cp, mul(mload(add(SI, mul(add(3, mul(pr, 2)), 32))), 32)))
                let num := add(mulmod(shr(128, wN), and(wD, MASK), modulus), mulmod(and(wN, MASK), shr(128, wD), modulus))
                let den := mulmod(shr(128, wD), and(wD, MASK), modulus)
                g := add(mulmod(gb, num, modulus), g)
                gb := mulmod(gb, batching, modulus)
                g := add(mulmod(gb, den, modulus), g)
                gb := mulmod(gb, batching, modulus)
            }
            for { let step := 8 } lt(step, 10) { step := add(step, 1) } {
                let word := mload(add(cp, mul(mload(add(SI, mul(step, 32))), 32)))
                g := add(mulmod(gb, mulmod(shr(128, word), and(word, MASK), modulus), modulus), g)
                gb := mulmod(gb, batching, modulus)
            }
            if mod(add(mulmod(mod(g, modulus), eq_scale, modulus), sub(modulus, claim)), modulus) {
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
                // absorbed above, so requiring both lanes < P makes any accepted proof's absorb
                // canonical
                if iszero(lt(a, modulus)) { revert(0, 0) }
                if iszero(lt(b, modulus)) { revert(0, 0) }
                mstore(add(GKR_CLAIMS_PTR(), mul(li, 32)), add(a, mulmod(add(b, sub(modulus, a)), r_last, modulus)))
            }
            ncp := add(cp, __TEMPLATE_GKR_LSB_LINES_BYTES)
        }

        // DIM_REDUCE_LAYERS dim-reducing layers (folding_steps OUTPUT_LOG2 .. trace_log2-1).
        // Reads the NUM_OUTPUTS claims + batching from gkr_init (GKR_CLAIMS_PTR /
        // GKR_BATCHING_PTR); reuses sumcheck_rounds for the monomial rounds.
        // Merged.t.sol checks acceptance and rejects tampered GKR proof bytes.
        function gkr_compress(ptr, claim0, alpha0) -> next_ptr, next_claim, next_alpha {
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
                claim := mod(claim, mload(P_PTR))
                let eq_scale
                ptr, claim,
                eq_scale := sumcheck_rounds(ptr, claim, fs)
                ptr,
                batching := gkr_dr_final(ptr, fs, batching, eq(add(k, 1), __TEMPLATE_GKR_DIM_REDUCE_LAYERS), eq_scale, claim)
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
                    let cv := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, wk))))
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
                    let cv := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, wk))))
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
                    let cv := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, wk))))
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
                    let cv := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, wk))))
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
            mcopy(bp, add(base, mul(16, 0)), mul(16, 8))
            bp := add(bp, mul(16, 8))
            mcopy(bp, add(base, mul(16, 48)), mul(16, 26))
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
            mcopy(bp, add(base, mul(16, 8)), mul(16, 40))
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
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 8)))))), add(0, 0)), add(0, 0)), add(0, 0)), add(0, 0)), add(0, 0)), add(0, 0)), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 11)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 10)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 9))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (0 + 1[13]) + (0 + 1[14]) + (0 + 1[15]) + (0 + 1[16]) + (0 + 1[17]) + (0 + 1[18]) + (0 + 1[19]) + (0 + 1[20]) + (0 + 0) + (0 + 1[12]) = Cache(1)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 12)))))), add(0, 0)), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 20)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 19)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 18)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 17)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 16)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 15)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 14)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 13))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (0 + 1[22]) + (0 + 1[23]) + (0 + 1[24]) + (0 + 1[25]) + (0 + 1[26]) + (0 + 1[27]) + (0 + 1[28]) + (0 + 1[29]) + (0 + 0) + (0 + 1[21]) = Cache(2)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 21)))))), add(0, 0)), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 29)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 28)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 27)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 26)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 23)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 22))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (0 + 1[31]) + (0 + 1[32]) + (0 + 1[33]) + (0 + 1[34]) + (0 + 1[35]) + (0 + 1[36]) + (0 + 1[37]) + (0 + 1[38]) + (0 + 0) + (0 + 1[30]) = Cache(3)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 30)))))), add(0, 0)), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 38)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 37)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 36)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 35)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 34)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 33)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 32)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 31))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookup: (0 + 1[40]) + (0 + 1[41]) + (0 + 1[42]) + (0 + 1[43]) + (0 + 1[44]) + (0 + 1[45]) + (0 + 1[46]) + (0 + 1[47]) + (0 + 0) + (0 + 1[39]) = Cache(4)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 39)))))), add(0, 0)), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 47)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 46)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 45)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 44)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 43)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 42)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 41)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 40))))))
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
            mstore(add(GKR_GATEVAL_PTR(), mul(32, 29)), 0x380000000000000000000000000)
            mstore(add(GKR_GATEVAL_PTR(), mul(32, 30)), 0x37ffe4000000000000000000000)
            mstore(add(GKR_GATEVAL_PTR(), mul(32, 77)), 0x7800000100000000)
            extcodecopy(__TEMPLATE_F1_FRONTIER, GKR_QTABLE_PTR(), __TEMPLATE_F1_DATA_QTABLE_OFFSET, 3360)
            // accumulate every term into gateval[gate_slot], one loop per bucket
            {
            let modulus := P
            let col_base := mload(CIRCUIT_PTR) // calldata base of the column at-point evals
            let gateval := GKR_GATEVAL_PTR()
            // linear    terms, coeff  1B positive  (68 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 0) let rec_end := add(rec_ptr, 204)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 3) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(232, rec), 0xff), shr(128, mload(add(col_base, mul(16, byte(1, rec))))), modulus), modulus))
            } }
            // linear    terms, coeff  2B positive  (4 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 204) let rec_end := add(rec_ptr, 16)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 4) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(224, rec), 0xffff), shr(128, mload(add(col_base, mul(16, byte(1, rec))))), modulus), modulus))
            } }
            // linear    terms, coeff 16B canonical (6 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 220) let rec_end := add(rec_ptr, 108)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 18) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(112, rec), MASK), shr(128, mload(add(col_base, mul(16, byte(1, rec))))), modulus), modulus))
            } }
            // linear    terms, coeff  1B negative  (59 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 328) let rec_end := add(rec_ptr, 177)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 3) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(sub(modulus, and(shr(232, rec), 0xff)), shr(128, mload(add(col_base, mul(16, byte(1, rec))))), modulus), modulus))
            } }
            // quadratic terms, coeff  1B positive  (328 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 505) let rec_end := add(rec_ptr, 1312)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 4) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(224, rec), 0xff), mulmod(shr(128, mload(add(col_base, mul(16, byte(1, rec))))), shr(128, mload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff  2B positive  (16 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 1817) let rec_end := add(rec_ptr, 80)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 5) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(216, rec), 0xffff), mulmod(shr(128, mload(add(col_base, mul(16, byte(1, rec))))), shr(128, mload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff  4B positive  (14 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 1897) let rec_end := add(rec_ptr, 98)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 7) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(200, rec), 0xffffffff), mulmod(shr(128, mload(add(col_base, mul(16, byte(1, rec))))), shr(128, mload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff 16B canonical (30 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 1995) let rec_end := add(rec_ptr, 570)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 19) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(and(shr(104, rec), MASK), mulmod(shr(128, mload(add(col_base, mul(16, byte(1, rec))))), shr(128, mload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff  1B negative  (113 records)
            { let rec_ptr := add(GKR_QTABLE_PTR(), 2565) let rec_end := add(rec_ptr, 452)
            for { } lt(rec_ptr, rec_end) { rec_ptr := add(rec_ptr, 4) } {
                let rec := mload(rec_ptr)
                let gate_ptr := add(gateval, mul(32, byte(0, rec)))
                mstore(gate_ptr, addmod(mload(gate_ptr), mulmod(sub(modulus, and(shr(224, rec), 0xff)), mulmod(shr(128, mload(add(col_base, mul(16, byte(1, rec))))), shr(128, mload(add(col_base, mul(16, byte(2, rec))))), modulus), modulus), modulus))
            } }
            // quadratic terms, coeff  4B negative  (48 records)
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
    let rhs_scaled := mulmod(acc, eq_scale, mload(P_PTR))
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(mload(P_PTR), rhs_scaled)), mload(P_PTR)) { revert(0, 0) }

    
            // canonicity guard for the base-layer claims_batch absorb: 106 at-point evals from
            // calldata; require each < P so the absorbed transcript bytes are canonical
                for { let wk := 0 } lt(wk, 106) { wk := add(wk, 1) } {
                    if iszero(lt(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, wk)))), mload(P_PTR))) { revert(0, 0) }
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // absorb final_step ++ extras in one keccak, THEN draw). next_claim unused (sccl recomputes).
    {
            let base := mload(CIRCUIT_PTR)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            let bp := add(GKR_ABS_PTR(), 32)
            // absorb final_step ++ extras contiguously, then draw (soundness: batching depends on
            // the extra cache-dependency evals). ONE keccak of [seed || final_step || extras].
            mcopy(bp, add(base, mul(16, 38)), mul(16, 58))
            bp := add(bp, mul(16, 58))
            mcopy(bp, add(base, mul(16, 2)), mul(16, 2))
            bp := add(bp, mul(16, 2))
            mcopy(bp, add(base, mul(16, 5)), mul(16, 7))
            bp := add(bp, mul(16, 7))
            mcopy(bp, add(base, mul(16, 14)), mul(16, 24))
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
            mcopy(bp, add(base, mul(16, 0)), mul(16, 2))
            bp := add(bp, mul(16, 2))
            mcopy(bp, add(base, mul(16, 4)), mul(16, 1))
            bp := add(bp, mul(16, 1))
            mcopy(bp, add(base, mul(16, 12)), mul(16, 2))
            bp := add(bp, mul(16, 2))
            mcopy(bp, add(base, mul(16, 96)), mul(16, 10))
            bp := add(bp, mul(16, 10))
            let s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR()))
            mstore(SEED_PTR(), s)
            s := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), s)
            next_alpha := mod(shr(128, s), mload(P_PTR))
            next_ptr := add(ptr, mul(16, 106))
            next_claim := 0
            }
}

            function scl0_caches() {
    {  // MemoryTuple: (γ + 0 + α[4] + α²0 + α³(0 + [0]) + α⁴[1] + α⁵[2] + α⁶[3]) = Cache(0)
        let gate := add(gkr_memrel_compress_low(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 4)))), 0), gkr_memrel_compress_high(add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 0))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 1)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 3))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + [9] + α[10] + α²[11] + α³(0 + [5]) + α⁴[6] + α⁵[7] + α⁶[8]) = Cache(1)
        let gate := add(gkr_memrel_compress_low(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 10)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 11))))), gkr_memrel_compress_high(add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 5))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 6)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 7)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 8))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + 0 + α[4] + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[2] + α⁶[3]) = Cache(2)
        let gate := add(gkr_memrel_compress_low(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 4)))), 0), gkr_memrel_compress_high(add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 3))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + [9] + α[10] + α²[11] + α³(1 + [24]) + α⁴[25] + α⁵[7] + α⁶[8]) = Cache(3)
        let gate := add(gkr_memrel_compress_low(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 10)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 11))))), gkr_memrel_compress_high(add(1, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 7)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 8))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + [16] + α[17] + α²[18] + α³(0 + [12]) + α⁴[13] + α⁵[14] + α⁶[15]) = Cache(4)
        let gate := add(gkr_memrel_compress_low(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 17)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 18))))), gkr_memrel_compress_high(add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 12))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 13)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 14)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 15))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + 2 + α0 + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[22] + α⁶[23]) = Cache(5)
        let gate := add(gkr_memrel_compress_low(2, 0, 0), gkr_memrel_compress_high(add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 22)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 23))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 5)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + [16] + α[17] + α²[18] + α³(2 + [24]) + α⁴[25] + α⁵[19] + α⁶[20]) = Cache(6)
        let gate := add(gkr_memrel_compress_low(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 17)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 18))))), gkr_memrel_compress_high(add(2, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 19)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 20))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 6)), mod(gate, mload(P_PTR)))
    }
    {  // MemoryTuple: (γ + 2 + α0 + α²0 + α³(0 + [28]) + α⁴[29] + α⁵[26] + α⁶[27]) = Cache(7)
        let gate := add(gkr_memrel_compress_low(2, 0, 0), gkr_memrel_compress_high(add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 28))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 29)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 26)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 27))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 7)), mod(gate, mload(P_PTR)))
    }
    {  // SingleColumnLookup: 0 + -1[24] + 1[0] + 2^19[90] = Cache(8)
        let gate := add(0, add(add(mulmod(sub(mload(P_PTR), 1), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 24)))), mload(P_PTR)), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 0))))), mulmod(524288, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 90)))), mload(P_PTR))))
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
    {  // VectorizedLookup: (0 + 1[22]) + (0 + 1[23]) + (0 + 1[4]) + (0 + 1[38]) + (0 + 1[39]) + (0 + 1[40]) + (0 + 1[41]) + (0 + 1[42]) + (0 + 1[43] + 2[44] + 2^2[45] + 2^3[46] + 2^4[47] + 2^5[48] + 2^6[49] + 2^7[50] + 2^8[51] + 2^9[52] + 2^10[53] + 2^11[54] + 2^12[55] + 2^13[56] + 2^14[57] + 2^15[58] + 2^16[59] + 2^17[9] + 2^18[16]) + (46 + 0) = Cache(14)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(46, 0)), add(0, add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 43)))), mulmod(2, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 44)))), mload(P_PTR))), mulmod(4, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 45)))), mload(P_PTR))), mulmod(8, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 46)))), mload(P_PTR))), mulmod(16, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 47)))), mload(P_PTR))), mulmod(32, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 48)))), mload(P_PTR))), mulmod(64, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 49)))), mload(P_PTR))), mulmod(128, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mload(P_PTR))), mulmod(256, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 51)))), mload(P_PTR))), mulmod(512, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 52)))), mload(P_PTR))), mulmod(1024, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mload(P_PTR))), mulmod(2048, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mload(P_PTR))), mulmod(4096, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mload(P_PTR))), mulmod(8192, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mload(P_PTR))), mulmod(16384, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 57)))), mload(P_PTR))), mulmod(32768, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mload(P_PTR))), mulmod(65536, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mload(P_PTR))), mulmod(131072, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mload(P_PTR))), mulmod(262144, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mload(P_PTR))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 42)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 41)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 40)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 39)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 38)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 4)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 23)))))), add(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 22))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 14)), mod(gate, mload(P_PTR)))
    }
    {  // VectorizedLookupSetup: β⁰[96] + β¹[97] + β²[98] + β³[99] + β⁴[100] + β⁵[101] + β⁶[102] + β⁷[103] + β⁸[104] + β⁹[105] = Cache(15)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 105))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 104))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 103))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 102))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 101))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 100))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 99))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 98))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 97))))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 96)))))
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
        let gate := gkr_virtual_poly_compose_vars(7, 14)
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
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 79 } lt(s, 82) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

            }
            function scl0_g8(alpha, a) -> acc { acc := a
            { let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()
            for { let s := 82 } lt(s, 94) { s := add(s, 1) } {
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
            for { let s := 118 } lt(s, 120) { s := add(s, 1) } {
                acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))
            } }

    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[0]<<7)) + α³[32] + α⁴[33] + α⁵[30] + α⁶[31]) * (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[1]<<7)) + α³[36] + α⁴[37] + α⁵[34] + α⁶[35]) = 6
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR(), mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))), mload(P_PTR)))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(7, __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_0)), mload(P_PTR)), gkr_memrel_compress_high(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 32)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 33)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 30)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 31))))))) // for memrel we collect
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(7, __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_1)), mload(P_PTR)), gkr_memrel_compress_high(shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 36)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 37)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 34)))), shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, 35))))))) // for memrel we collect
        let gate := mulmod(lhs, rhs, mload(P_PTR))
        acc := add(mulmod(acc, alpha, mload(P_PTR)), gate)
    }
    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[0]<<7)) + 0) * (γ + 1 + αCache(18) + α²(Cache(19) + (topbits[1]<<7)) + 0) = 5
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR(), mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))), mload(P_PTR)))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(7, __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_0)), mload(P_PTR)), 0)) // for memrel we collect
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), shl(7, __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_1)), mload(P_PTR)), 0)) // for memrel we collect
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
    // E1 (see sumcheck_rounds): (b, c) in, c0..c3 rebuilt and absorbed, claim = K, eq_scale = 1
    let bit := mload(ptr)
    for { let i := 0 } lt(i, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS) { i := add(i, 1) } {
        let zp := add(POINT_PTR(), mul(i, 32))
        let r
        r, claim := f1_e1_round(bit, mload(zp), claim, modulus)
        bit := add(bit, 246)
        mstore(zp, r)
        ptr := add(ptr, 64)
    }
    next_ptr := ptr
    next_claim := claim
}
function transcriptNTo1(ptr, input_elements) -> alpha {
    let input_bytes := mul(input_elements, 16)
    mcopy(add(SEED_PTR(), 32), ptr, input_bytes)
    let seed := keccak256(SEED_PTR(), add(32, input_bytes)) // absorb evals
    mstore(SEED_PTR(), seed)
    seed := keccak256(SEED_PTR(), 32)                       // draw (the mirror draws a fresh el)
    mstore(SEED_PTR(), seed)
    alpha := mod(shr(128, seed), mload(P_PTR))                         // batching is a field element mod P
}
function sumcheck_claims_batch(ptr, points) -> next_ptr, next_claim, next_alpha {
    let is_odd := mod(points, 2)
    if is_odd {
        next_claim := shr(128, mload(add(ptr, mul(16, sub(points, 1)))))
    }
    next_alpha := transcriptNTo1(ptr, points)
    let even_points := sub(points, is_odd)
    let pairs := shr(1, even_points)
    for { let pair := sub(pairs, 1) } lt(pair, pairs) { pair := sub(pair, 1) } {
        let word := mload(add(ptr, mul(pair, 32)))
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
    load := shr(128, mload(add(mload(CIRCUIT_PTR), mul(16, idx))))
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

        // Copy `count` little-endian u32s from calldata[cdpos] to memory[wpos] as big-endian.
        // The GKR preimage stores the merkle caps as LE u32; the WHIR half wants BE u32
        // digests, so each 4-byte word is byte-reversed.
        function write_cap_be(wpos, cdpos, count) {
            for { let j := 0 } lt(j, count) { j := add(j, 1) } {
                let le := shr(224, mload(add(F1_V0_PTR(), add(cdpos, mul(4, j)))))
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
        // Fold one PACK = 2^PACK_LOG2 chunk (count real evals from calldata, rest zero) by the
        // PACK_LOG2 packing coords at `ex` — a PACK_LOG2-var multilinear eval → single claim.
        // LSB binding: adjacent evals differ in pack-index bit 0, which pairs with ex[0], so the
        // coords apply FORWARD (mirrors the prover's merge_claims). Scratch: PACK slots at
        // ABS+FOLD_OFFSET (the generator sizes the ABS region for it).
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
        // LE at preimage byte reg*PREIMAGE_REGISTER_STRIDE; the preimage is at calldata 0),
        // concatenated in register order. Assembled in the 0x00 scratch word.
        function mark_word(first_reg) -> w {
            for { let i := 0 } lt(i, MARK_WORD_REGISTERS) { i := add(i, 1) } {
                mcopy(mul(i, 4), add(F1_V0_PTR(), mul(add(first_reg, i), PREIMAGE_REGISTER_STRIDE)), 4)
            }
            w := mload(0)
        }

        // GKR→WHIR handoff: draw the PACK_LOG2 packing coords, merge the base-layer claims
        // (mem++wit NUM_MEMWIT→MERGED_MW, setup NUM_SETUP→SETUP_MERGED), draw the WHIR batching challenge
        // (PoW), form the batched opening, and write the WHIR half's start state straight into
        // its memory regions: seed, batching, opening, z = base_z(BASE_Z_COORDS) ++
        // extra(PACK_LOG2), the two base-oracle caps (the pack index occupies the HIGH bits of
        // the packed enumeration, so under LSB binding the packing coords EXTEND the claim point
        // at the top). Own frame — keeps the fallback stack under the EVM limit. `ptr` is the GKR stream cursor after the circuit layers: it points at the
        // 8-byte WHIR-batching PoW nonce; the WHIR proof stream follows it.
        function emit_gkr_mark(claim_v, ptr) {
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
            let wnonce := shr(192, mload(ptr))
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
            for { let i := 0 } lt(i, add(__TEMPLATE_WHIR_MERGED_MW, __TEMPLATE_WHIR_SETUP_MERGED)) { i := add(i, 1) } {
                opening := addmod(opening, mulmod(mload(add(mg, mul(32, i))), bexp, mload(P_PTR)), mload(P_PTR))
                bexp := mulmod(bexp, batching, mload(P_PTR))
            }
            // Hand the WHIR start state over in memory (the __TEMPLATE_WHIR_* regions are the
            // WHIR half's, laid out by the generator). Layout mirrors what the WHIR half consumes.
            mstore(__TEMPLATE_WHIR_SEED_PTR, seed)
            mstore(__TEMPLATE_WHIR_HANDOFF_BATCHING_PTR, batching)
            mstore(__TEMPLATE_WHIR_REG_CLAIM, opening)
            // z = base_z(BASE_Z_COORDS) ++ packing coords, one 128-bit value per slot
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_BASE_Z_COORDS) { i := add(i, 1) } {
                mstore(add(__TEMPLATE_WHIR_Z_PTR, mul(i, 32)), and(mload(add(POINT_PTR(), mul(i, 32))), MASK))
            }
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_PACK_LOG2) { i := add(i, 1) } {
                mstore(add(__TEMPLATE_WHIR_Z_PTR, mul(add(__TEMPLATE_WHIR_BASE_Z_COORDS, i), 32)), and(mload(add(ex, mul(32, i))), MASK))
            }
            // caps: the WHIR half wants [memory_cap][setup_cap] as BE u32 digests. The GKR
            // preimage (calldata 0) holds them as LE u32 at the generated PREIMAGE_*_CAP offsets;
            // re-encode to BE (write_cap_be). count = CAP*8 u32s per cap.
            write_cap_be(__TEMPLATE_WHIR_BCAP0_PTR, __TEMPLATE_PREIMAGE_MEMORY_CAP_OFFSET, mul(__TEMPLATE_WHIR_CAP, 8))  // memory
            write_cap_be(__TEMPLATE_WHIR_BCAP1_PTR, __TEMPLATE_PREIMAGE_SETUP_CAP_OFFSET, mul(__TEMPLATE_WHIR_CAP, 8))   // setup
        }

        // Every checked WHIR relation flows through here: revert unless equal.
        function sink2(a, b) { if iszero(eq(a, b)) { revert(0, 0) } }
        function draw1() -> r {
            let s := keccak256(__TEMPLATE_WHIR_SEED_PTR, 32)
            mstore(__TEMPLATE_WHIR_SEED_PTR, s)
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
        function f1_fe(cd, i) -> v {
            let bit := mul(123, i)
            v := and(shr(sub(133, and(bit, 7)), calldataload(add(cd, shr(3, bit)))), 0x7ffffffffffffffffffffffffffffff)
            if iszero(lt(v, P)) { revert(0, 0) }
        }
        function f1_word(cd, bit) -> w {
            let x := shr(sub(10, and(bit, 7)), calldataload(add(cd, shr(3, bit))))
            let a := and(shr(123, x), 0x7ffffffffffffffffffffffffffffff)
            let b := and(x, 0x7ffffffffffffffffffffffffffffff)
            if or(iszero(lt(a, P)), iszero(lt(b, P))) { revert(0, 0) }
            w := or(shl(128, a), b)
        }
        function f1_run_end(cd, n) -> next_cd {
            let bits := mul(123, n)
            next_cd := add(cd, shr(3, add(bits, 7)))
            // All cursor advances are profile-derived; the final REG_CD equality rejects overruns.
            let pad := and(sub(0, bits), 7)
            if pad {
                if and(byte(0, calldataload(sub(next_cd, 1))), sub(shl(pad, 1), 1)) { revert(0, 0) }
            }
        }
        function f1_digest(cp) -> d {
            d := and(calldataload(cp), 0xffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000)
        }
        function verify_pow(cp, pow_bits) -> next_cd {
            let nonce := shr(192, calldataload(cp))
            mstore(add(__TEMPLATE_WHIR_SEED_PTR, 32), shl(192, nonce))
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
                for { let j := 0 } and(lt(j, 8), lt(wi, padded)) { j := add(j, 1) } {
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
        // inverse (matches prover `initial_high_powers_offsets`). set_generator =
        // domain_generator_for_size(2^fold) = __TEMPLATE_WHIR_GEN^(2^(codeword_log2 - fold)), and
        // qib = codeword_log2 - fold, so set_gen_inv = __TEMPLATE_WHIR_GEN_INV^(2^qib) = exp_pow2(__TEMPLATE_WHIR_GEN_INV, qib).
        // hp[i] = set_gen_inv^i, then the length-2^(fold-1) array is bit-reversed.
        function compute_hpo(fold, qib) {
            let logc := sub(fold, 1)         // log2(count)
            // forge-lint: disable-next-line(incorrect-shift) — `shl(n, 1)` is `1 << n` (2^n), args are correct
            let count := shl(logc, 1)
            let sgi := exp_pow2(__TEMPLATE_WHIR_GEN_INV, qib) // order-2^fold generator inverse
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
                    // reduce on load: with eval_leaves the buffer holds raw (possibly >= P)
                    // calldata lanes, and `sub(P, b)` below must see a canonical b
                    let a := mod(mload(add(__TEMPLATE_WHIR_FBUF_PTR, mul(mul(i, 2), 32))), P)
                    let b := mod(mload(add(__TEMPLATE_WHIR_FBUF_PTR, mul(add(mul(i, 2), 1), 32))), P)
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
        // Merkle path of `depth` levels (already cap-reduced), then match a cap
        // entry. depth = query_index_bits - __TEMPLATE_WHIR_CAP_LOG2.
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
            // cap_ptr 0 = the setup frontier: the walk stops LEVEL bits below the root, not CAP_LOG2
            let top_bits := __TEMPLATE_WHIR_CAP_LOG2
            if iszero(cap_ptr) { top_bits := __TEMPLATE_F1_FRONTIER_LEVEL }
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
                    let sibling := f1_digest(cp)
                    cp := add(cp, __TEMPLATE_F1_DIGEST_BYTES)
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
                // frontier[cap_index], after the data contract's leading STOP byte
                extcodecopy(__TEMPLATE_F1_FRONTIER, 0, add(1, mul(__TEMPLATE_F1_DIGEST_BYTES, cap_index)), __TEMPLATE_F1_DIGEST_BYTES)
                sink2(h, and(mload(0), __TEMPLATE_DIGEST_MASK))
            }
            default { sink2(h, mload(add(cap_ptr, mul(cap_index, 32)))) }
            next_cd := cp
        }
        function batch_oracle(cp, cols, goff, vp, depth, cap_ptr, qidx, cb) -> next_cd {
            let wpc := shr(1, vp)
            let li := 0
            let bit := 0
            for { let c := 0 } lt(c, cols) { c := add(c, 1) } {
                let gamma := mload(add(__TEMPLATE_WHIR_GAMMA_PTR, mul(add(goff, c), 32)))
                for { let wj := 0 } lt(wj, wpc) { wj := add(wj, 1) } {
                    let w := f1_word(cp, bit)
                    bit := add(bit, 246)
                    mstore(add(__TEMPLATE_WHIR_LEAF_PTR, mul(li, 32)), w)
                    li := add(li, 1)
                    let s0 := add(__TEMPLATE_WHIR_FBUF_PTR, mul(mul(wj, 2), 32))
                    let s1 := add(__TEMPLATE_WHIR_FBUF_PTR, mul(add(mul(wj, 2), 1), 32))
                    mstore(s0, addmod(mload(s0), mulmod(gamma, shr(128, w), P), P))
                    mstore(s1, addmod(mload(s1), mulmod(gamma, and(w, MASK), P), P))
                }
            }
            cp := f1_run_end(cp, mul(cols, vp))
            next_cd := merkle_path(and(keccak256(__TEMPLATE_WHIR_LEAF_PTR, mul(li, 32)), __TEMPLATE_DIGEST_MASK), depth, cap_ptr, cp, qidx, cb)
        }
        function read_leaf(cp, vp, depth, cap_ptr, qidx, cb) -> next_cd {
            let words := shr(1, vp)
            let bit := 0
            for { let i := 0 } lt(i, words) { i := add(i, 1) } {
                let w := f1_word(cp, bit)
                bit := add(bit, 246)
                mstore(add(__TEMPLATE_WHIR_LEAF_PTR, mul(i, 32)), w)
                mstore(add(__TEMPLATE_WHIR_FBUF_PTR, mul(mul(i, 2), 32)), shr(128, w))
                mstore(add(__TEMPLATE_WHIR_FBUF_PTR, mul(add(mul(i, 2), 1), 32)), and(w, MASK))
            }
            cp := f1_run_end(cp, vp)
            next_cd := merkle_path(and(keccak256(__TEMPLATE_WHIR_LEAF_PTR, mul(words, 32)), __TEMPLATE_DIGEST_MASK), depth, cap_ptr, cp, qidx, cb)
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

        function do_query(r, fold, qib, vp, idx_mask, delin, cb, qq) {
            let cp := mload(__TEMPLATE_WHIR_REG_CD)
            let cur := mulmod(mload(__TEMPLATE_WHIR_REG_CURDELIN), delin, P)
            mstore(__TEMPLATE_WHIR_REG_CURDELIN, cur)
            let qidx := and(mload(add(__TEMPLATE_WHIR_QIDX_BUF_PTR, mul(qq, 32))), idx_mask)
            let base_root_inv := powmod(__TEMPLATE_WHIR_GEN_INV, qidx)
            let depth := sub(qib, __TEMPLATE_WHIR_CAP_LOG2)

            switch r
            case 0 {
                // Round 0 queries the base oracles: 7 witness columns (BCAP0) then
                // 1 setup column (BCAP1), gamma-batched into the folding buffer.
                // (7 = merged memory+witness packed columns; setup at gamma-power 7.)
                for { let j := 0 } lt(j, vp) { j := add(j, 1) } { mstore(add(__TEMPLATE_WHIR_FBUF_PTR, mul(j, 32)), 0) }
                cp := batch_oracle(cp, __TEMPLATE_WHIR_MERGED_MW, 0, vp, depth, __TEMPLATE_WHIR_BCAP0_PTR, qidx, cb)
                cp := batch_oracle(cp, __TEMPLATE_WHIR_SETUP_MERGED, __TEMPLATE_WHIR_MERGED_MW, vp, sub(depth, __TEMPLATE_F1_FRONTIER_SKIP), 0, qidx, cb)
            }
            default {
                cp := read_leaf(cp, vp, depth, __TEMPLATE_WHIR_QCAP_PTR, qidx, cb)
            }
            mstore(__TEMPLATE_WHIR_REG_CD, cp)
            // round 0 queries a base oracle (coset fold); later rounds query
            // intermediate oracles (plain multilinear fold, no base-root).
            let folded
            // round 0 (base oracle) always folds evals with the coset base-root;
            // intermediate rounds fold coeff leaves (fold_multilinear) unless the
            // prover used eval_leaves, in which case they too are raw evals.
            switch or(iszero(r), W_EVAL_LEAVES)
            case 1 { folded := fold_coset(fold, base_root_inv) }
            default { folded := fold_multilinear(fold) }
            push_pow(exp_pow2(powmod(__TEMPLATE_WHIR_GEN, qidx), fold), cur)
            mstore(__TEMPLATE_WHIR_REG_CC, addmod(mload(__TEMPLATE_WHIR_REG_CC), mulmod(folded, cur, P), P))
        }

        function do_internal(r, fold, q, pow_bits, qib, vp, idx_mask, cb) {
            let cp := mload(__TEMPLATE_WHIR_REG_CD)
            // read + absorb the next oracle's __TEMPLATE_WHIR_CAP (__TEMPLATE_WHIR_CAP*32 bytes)
            // keep BE digests for Merkle roots; absorb LE-word copies (commit_u32)
            for { let i := 0 } lt(i, __TEMPLATE_WHIR_CAP) { i := add(i, 1) } {
                let d := f1_digest(add(cp, mul(i, __TEMPLATE_F1_DIGEST_BYTES)))
                mstore(add(__TEMPLATE_WHIR_NCAP_PTR, mul(i, 32)), d)
                mstore(add(__TEMPLATE_WHIR_SEED_PTR, add(32, mul(i, 32))), bswap_digest(d))
            }
            mstore(__TEMPLATE_WHIR_SEED_PTR, keccak256(__TEMPLATE_WHIR_SEED_PTR, add(32, mul(__TEMPLATE_WHIR_CAP, 32))))
            cp := add(cp, mul(__TEMPLATE_WHIR_CAP, __TEMPLATE_F1_DIGEST_BYTES))
            let ood_point := draw1()
            let ood_value := shr(128, calldataload(cp))
            // reject a non-canonical (>= P) ood_value: it is absorbed as raw bytes below,
            // so the transcript must bind to the reduced value
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
            compute_hpo(fold, qib)
            for { let qq := 0 } lt(qq, q) { qq := add(qq, 1) } {
                do_query(r, fold, qib, vp, idx_mask, delin, cb, qq)
            }
            mstore(__TEMPLATE_WHIR_REG_CLAIM, addmod(mload(__TEMPLATE_WHIR_REG_CLAIM), mload(__TEMPLATE_WHIR_REG_CC), P))
            copy_cap(__TEMPLATE_WHIR_QCAP_PTR, __TEMPLATE_WHIR_NCAP_PTR) // this round's intermediate cap is next round's query cap
        }

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
        function do_final(fold, q, pow_bits, qib, vp, idx_mask, zi_off, rfin, cb) {
            // forge-lint: disable-next-line(incorrect-shift) — `shl(n, 1)` is `1 << n` (2^n), args are correct
            let nmono := shl(rfin, 1)
            let cp := mload(__TEMPLATE_WHIR_REG_CD)
            // absorb via the large FEVAL scratch: 32 + nmono*16 bytes would
            // overrun the SEED region (into z / pow) for the 2^8 tail
            mstore(__TEMPLATE_WHIR_FEVAL_PTR, mload(__TEMPLATE_WHIR_SEED_PTR))
            {
            let bit := 0
            for { let wj := 0 } lt(wj, shr(1, nmono)) { wj := add(wj, 1) } {
                mstore(add(__TEMPLATE_WHIR_FEVAL_PTR, add(32, mul(wj, 32))), f1_word(cp, bit))
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
            cp := f1_run_end(cp, nmono)
            cp := verify_pow(cp, pow_bits)
            draw_queries(q, qib)
            compute_hpo(fold, qib)
            let depth := sub(qib, __TEMPLATE_WHIR_CAP_LOG2)

            for { let qq := 0 } lt(qq, q) { qq := add(qq, 1) } {
                let qidx := and(mload(add(__TEMPLATE_WHIR_QIDX_BUF_PTR, mul(qq, 32))), idx_mask)
                let base_root := powmod(__TEMPLATE_WHIR_GEN, qidx)
                cp := read_leaf(cp, vp, depth, __TEMPLATE_WHIR_QCAP_PTR, qidx, cb)
                // final round queries an intermediate oracle: coeff leaves fold with
                // the plain monomial tensor, unless eval_leaves (raw evals -> fold_coset).
                let folded
                switch W_EVAL_LEAVES
                case 1 { folded := fold_coset(fold, powmod(__TEMPLATE_WHIR_GEN_INV, qidx)) }
                default { folded := fold_multilinear(fold) }
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
        // written the start state (seed / batching / opening / z / base caps) into the regions
        // above. `cd_start` = calldata offset of the WHIR proof stream (right after the GKR
        // stream's trailing 8-byte WHIR-batching PoW nonce).
        function whir_verify(cd_start) {
        // Base geometry (all generated): nz = z-coords, gcount = gamma-batched base columns + 1,
        // rfin = final-poly log2.
        let nz := __TEMPLATE_WHIR_NZ
        let gcount := __TEMPLATE_WHIR_GCOUNT
        let rfin := __TEMPLATE_WHIR_RFIN
        let batching := mload(__TEMPLATE_WHIR_HANDOFF_BATCHING_PTR)

        // gamma powers
        mstore(__TEMPLATE_WHIR_GAMMA_PTR, 1)
        {
            let g := 1
            for { let i := 1 } lt(i, gcount) { i := add(i, 1) } {
                g := mulmod(g, batching, P)
                mstore(add(__TEMPLATE_WHIR_GAMMA_PTR, mul(i, 32)), g)
            }
        }

        mstore(__TEMPLATE_WHIR_ACC_PREF_PTR, 1)
        mstore(__TEMPLATE_WHIR_REG_NUMPOW, 0)
        mstore(__TEMPLATE_WHIR_REG_ZIOFF, 0)
        mstore(__TEMPLATE_WHIR_REG_CD, cd_start) // the WHIR proof stream starts right after the GKR stream

        for { let r := 0 } lt(r, __TEMPLATE_WHIR_NUM_ROUNDS) { r := add(r, 1) } {
            // `cb` = coset bits = log2(LDE factor) for this round's oracle tree.
            let fold, q, pow_bits, qib, vp, cb
            switch r
            case 0 { fold := 1 q := 12 pow_bits := 30 qib := 30 vp := 2 cb := 7 }
            case 1 { fold := 4 q := 11 pow_bits := 27 qib := 27 vp := 16 cb := 8 }
            case 2 { fold := 4 q := 7 pow_bits := 30 qib := 27 vp := 16 cb := 12 }
            case 3 { fold := 4 q := 6 pow_bits := 20 qib := 27 vp := 16 cb := 16 }
            default { fold := 4 q := 5 pow_bits := 17 qib := 27 vp := 16 cb := 20 }
            // forge-lint: disable-next-line(incorrect-shift) — `shl(n, 1)` is `1 << n` (2^n), args are correct
            let idx_mask := sub(shl(qib, 1), 1)

            {
            let scbase := mload(__TEMPLATE_WHIR_REG_CD)
            mstore(__TEMPLATE_WHIR_REG_CD, f1_run_end(scbase, mul(2, fold)))
            let bit := 0
            for { let s := 0 } lt(s, fold) { s := add(s, 1) } {
                let pair := f1_word(scbase, bit)
                bit := add(bit, 246)
                let c0 := shr(128, pair)
                let c2 := and(pair, MASK)
                let c1 := addmod(mload(__TEMPLATE_WHIR_REG_CLAIM), sub(P, addmod(addmod(c0, c0, P), c2, P)), P)
                mstore(add(__TEMPLATE_WHIR_SEED_PTR, 32), or(shl(128, c0), c1))
                mstore(add(__TEMPLATE_WHIR_SEED_PTR, 64), shl(128, c2))
                mstore(__TEMPLATE_WHIR_SEED_PTR, keccak256(__TEMPLATE_WHIR_SEED_PTR, 80))
                let alpha := draw1()
                let p1 := addmod(c0, addmod(c1, c2, P), P)
                sink2(addmod(c0, p1, P), mload(__TEMPLATE_WHIR_REG_CLAIM))
                mstore(__TEMPLATE_WHIR_REG_CLAIM,
                    addmod(mulmod(addmod(mulmod(c2, alpha, P), c1, P), alpha, P), c0, P))
                mstore(add(__TEMPLATE_WHIR_FOLD_CH_PTR, mul(s, 32)), alpha)
                let zi_off := mload(__TEMPLATE_WHIR_REG_ZIOFF)
                fold_accumulator(alpha, mload(__TEMPLATE_WHIR_REG_NUMPOW), zi_off)
                mstore(__TEMPLATE_WHIR_REG_ZIOFF, add(zi_off, 32))
            }
            }

            switch lt(r, sub(__TEMPLATE_WHIR_NUM_ROUNDS, 1))
            case 1 { do_internal(r, fold, q, pow_bits, qib, vp, idx_mask, cb) }
            default { do_final(fold, q, pow_bits, qib, vp, idx_mask, mload(__TEMPLATE_WHIR_REG_ZIOFF), rfin, cb) }
        }

        // Hardening: the proof stream must be fully consumed — the cursor (__TEMPLATE_WHIR_REG_CD) must land
        // EXACTLY at the end of calldata, with no trailing/unused bytes. The WHIR stream is the
        // tail of the merged calldata; its last item is the final round's query openings.
        if iszero(eq(mload(__TEMPLATE_WHIR_REG_CD), calldatasize())) { revert(0, 0) }
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
            // the stream cursor is a memory address inside the v0 image
            f1_decode()
            ptr := transcript_init(F1_V0_PTR())
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

        // TODO: don't forget the recursion chain check
        // TODO: very, VERY, carefully review end-to-end fiat-shamir

        // ── GKR→WHIR handoff in memory, then the WHIR proximity check ─────────────────
        // emit_gkr_mark draws the packing coords + WHIR batching, merges the base-layer claims,
        // writes the WHIR start state into the __TEMPLATE_WHIR_* regions and stages the registry
        // payload; whir_verify then consumes the WHIR proof stream that follows the 8-byte
        // WHIR-batching PoW nonce at `ptr`, and requires its cursor to land exactly at
        // add(F1_V0_PTR(), 31524) — so the whole merged stream (GKR ‖ nonce ‖ WHIR) is checked for exact
        // consumption.
        emit_gkr_mark(claim, ptr)
        // F1: `ptr` is an image address; the WHIR stream follows the F1 GKR section
        whir_verify(20270)

        // SPILL OVERWRITE PREVENTION (re-checked after the WHIR half)
        if gt(mload(0x40), MINIMUM_FREE_HEAP_PTR) {
            revert(0, 0)
        }

        // The verified statement, handed to Solidity: publicInput = registers x10..x17,
        // auxInput = x18..x25 (u32 LE each, concatenated, from the preimage in calldata);
        // setupCommitment = keccak256 of the setup oracle's cap (CAP BE-u32 digests, still at
        // BCAP1 where emit_gkr_mark re-encoded them) — the circuit setup the proof was verified
        // against.
        publicInput := mark_word(PUBLIC_INPUT_FIRST_REGISTER)
        auxInput := mark_word(AUX_INPUT_FIRST_REGISTER)
        setupCommitment := keccak256(__TEMPLATE_WHIR_BCAP1_PTR, mul(__TEMPLATE_WHIR_CAP, 32))
        }
        // Report the verified statement; the registry (constructor-pinned, non-zero, has code)
        // must accept — its revert aborts the verification transaction.
        IVerificationRegistry(registry).markVerified(publicInput, auxInput, setupCommitment);
        return abi.encode(publicInput, auxInput, setupCommitment);
    }
}

// Generated heap map (byte offsets; every region sized from the circuit / prover config):
//     2112 ..   2336  MEMORY_CHALLS (32 * 7 = 224 B)
//     2336 ..   2400  LOGUP_CHALLS (32 * 2 = 64 B)
//     2400 ..   3072  POINT (32 * 21 = 672 B)
//     3072 ..   3104  INIT_GAS (32 = 32 B)
//     3104 ..   3136  MAIN_GAS (32 = 32 B)
//     3136 ..   4064  SEED (32 * 29 = 928 B)
//     4064 ..   4096  BATCHING (32 = 32 B)
//     4096 ..   4416  CLAIMS (32 * 10 = 320 B)
//     4416 ..   4736  EQ (32 * 10 = 320 B)
//     4736 ..   6784  ABS (32 * 64 = 2048 B)
//     6784 ..   6912  PERM_PROD (32 * 4 = 128 B)
//     6912 ..   9280  CIRCUIT_CLAIMS (32 * 74 = 2368 B)
//     9280 ..  13120  GATEVAL (32 * 120 = 3840 B)
//    13120 ..  16480  QTABLE (32 * 105 = 3360 B)
//    16480 ..  48032  F1_V0 (32 * 986 = 31552 B)
//    48032 ..  48320  SEED_PTR (32 + (1 << 3) * 32 = 288 B)
//    48320 ..  49088  Z_PTR (24 * 32 = 768 B)
//    49088 ..  52928  POW_PTR (40 * 96 = 3840 B)
//    52928 ..  52960  ACC_PREF_PTR (32 = 32 B)
//    52960 ..  53440  GAMMA_PTR (15 * 32 = 480 B)
//    53440 ..  53568  FOLD_CH_PTR (4 * 32 = 128 B)
//    53568 ..  53824  HPO_PTR ((1 << 3) * 32 = 256 B)
//    53824 ..  54336  FBUF_PTR ((1 << 4) * 32 = 512 B)
//    54336 ..  54784  LEAF_PTR (14 * 32 = 448 B)
//    54784 ..  54816  REG_CD (32 = 32 B)
//    54816 ..  54848  REG_CLAIM (32 = 32 B)
//    54848 ..  54880  REG_NUMPOW (32 = 32 B)
//    54880 ..  54912  REG_ZIOFF (32 = 32 B)
//    54912 ..  54944  REG_CC (32 = 32 B)
//    54944 ..  54976  REG_CURDELIN (32 = 32 B)
//    54976 ..  55008  HANDOFF_BATCHING_PTR (32 = 32 B)
//    55008 ..  55264  BCAP0_PTR ((1 << 3) * 32 = 256 B)
//    55264 ..  55520  BCAP1_PTR ((1 << 3) * 32 = 256 B)
//    55520 ..  55776  QCAP_PTR ((1 << 3) * 32 = 256 B)
//    55776 ..  56032  NCAP_PTR ((1 << 3) * 32 = 256 B)
//    56032 ..  56416  QIDX_BUF_PTR (12 * 32 = 384 B)
//    56416 ..  56928  DRAW_BUF_PTR (16 * 32 = 512 B)
//    56928 ..  61024  MONO_PTR ((1 << 7) * 32 = 4096 B)
//    61024 ..  65152  FEVAL_PTR (32 + (1 << 7) * 32 = 4128 B)
//   heap end: 65152
