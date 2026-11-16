//! GKR pieces of the wrap verifier: the generated calldata decoder, which writes the decoded GKR
//! image (the GKR proof in its uncompressed calldata layout) into memory, and the rewrite of every
//! other GKR calldata access into a read of that image. The `(b, c)` pairs of the factored rounds
//! stay in calldata; the round functions read them through `cd_load`.

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::merkle_trees::keccak256_hash_leafs::KECCAK256_MERKLE_DIGEST_BYTES as DIGEST_BYTES;

use crate::encoding::{fe_run_len, ts_run_len, Geometry};

/// Memory address of the decoded GKR image, as the Yul expression the rewritten readers use.
pub(crate) const IMAGE_PTR: &str = "IMAGE_PTR()";

/// Image bytes a factored-round run of `(b, c)` pairs occupies: one word, the run's calldata bit
/// offset.
pub(crate) const FACTORED_ROUND_SLOT_BYTES: usize = 32;

/// GKR output lines (5 output types × [read/num, write/den]).
const GKR_OUTPUTS: usize = 10;
const NUM_REGISTERS: usize = 32;

/// The decoder's layout: every run of the calldata's GKR section in stream order with its
/// destination in the decoded GKR image.
pub(crate) struct GkrDecoder {
    pub yul: String,
    /// The pinned setup cap as the decoded GKR image holds it (32 bytes per digest, LE u32
    /// words); the decoder copies it from the setup data contract.
    pub setup_cap_image: Vec<u8>,
    /// Length of the decoded GKR image.
    pub image_bytes: usize,
    /// Length of the calldata's GKR section (the WHIR stream starts here).
    pub calldata_bytes: usize,
}

/// `calldataload(x)` → `mload(x)`, `calldatacopy(d, x, n)` → `mcopy(d, x, n)`: the wrap
/// verifier's GKR stream cursor starts at [`IMAGE_PTR`], and the few absolute-offset readers add
/// [`IMAGE_PTR`] themselves. Panics on any other calldata opcode.
pub(crate) fn calldata_reads_to_image_reads(src: &str) -> String {
    fn close(src: &str, open: usize) -> usize {
        let mut depth = 0usize;
        for (i, ch) in src[open..].char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        return open + i;
                    }
                }
                _ => {}
            }
        }
        panic!("unbalanced parentheses after byte {open}");
    }
    fn top_level_commas(args: &str) -> Vec<usize> {
        let mut depth = 0usize;
        args.char_indices()
            .filter_map(|(i, ch)| {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    ',' if depth == 0 => return Some(i),
                    _ => {}
                }
                None
            })
            .collect()
    }
    let mut out = String::with_capacity(src.len() + src.len() / 8);
    let mut rest = src;
    let is_ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    while let Some(at) = rest.find("calldata") {
        out.push_str(&rest[..at]);
        let tail = &rest[at..];
        if out.chars().next_back().is_some_and(is_ident) {
            // inside a longer identifier
            out.push_str("calldata");
            rest = &tail["calldata".len()..];
        } else if let Some(op) = ["calldataload", "calldatacopy"]
            .into_iter()
            .find(|op| tail.starts_with(&format!("{op}(")))
        {
            let open = op.len();
            let end = close(tail, open);
            let args = calldata_reads_to_image_reads(&tail[open + 1..end]);
            if op == "calldataload" {
                out.push_str(&format!("mload({})", args.trim()));
            } else {
                let commas = top_level_commas(&args);
                assert_eq!(commas.len(), 2, "calldatacopy takes three arguments");
                let (dst, off, len) = (
                    &args[..commas[0]],
                    &args[commas[0] + 1..commas[1]],
                    &args[commas[1] + 1..],
                );
                out.push_str(&format!(
                    "mcopy({}, {}, {})",
                    dst.trim(),
                    off.trim(),
                    len.trim()
                ));
            }
            rest = &tail[end + 1..];
        } else {
            // identifiers and comments that merely mention calldata
            let word_end = tail.find(|c: char| !is_ident(c)).unwrap_or(tail.len());
            let word = &tail[..word_end];
            assert!(
                !matches!(word, "calldataload" | "calldatacopy" | "calldatasize"),
                "unexpected calldata access `{word}`"
            );
            out.push_str(word);
            rest = &tail[word_end..];
        }
    }
    out.push_str(rest);
    out
}

/// The decoder for `circuit` under `params`: `decode_calldata()` checks the GKR section's length
/// and every run's zero padding and writes the decoded GKR image at [`IMAGE_PTR`]: the preimage,
/// the nonces and every run's lanes; a factored-round run leaves only its bit offset in its
/// single image slot. Lanes are range-checked where they are read: the image lanes by the code
/// that reads the image, the `(b, c)` pairs by the round functions.
pub(crate) fn gkr_decoder(
    circuit: &GKRCircuitArtifact<Proth120>,
    params: &Geometry,
    final_pc: u32,
    setup_cap: &[[u32; 8]],
    top_bits: &[u32],
) -> GkrDecoder {
    let num_top_bits = top_bits.len();
    assert!(
        4 * num_top_bits <= 32,
        "the pinned top bits must fit one image word"
    );
    let cap = params.cap();
    let db = DIGEST_BYTES;
    assert_eq!(setup_cap.len(), cap, "setup cap size");
    let t = params.trace_log2;
    let e = params.explicit_output_log2;
    let num_mem = circuit.memory_layout.total_width;
    let num_wit = circuit.witness_layout.total_width;
    let num_setup = circuit.generic_lookup_tables_width;

    // Preimage lengths in the image and in the calldata: decode_calldata rebuilds the preimage
    // first; the rest of the GKR section is runs and raw bytes.
    let preimage_in_image = 12 * NUM_REGISTERS + 12 + 4 * num_top_bits + 2 * 32 * cap;
    let preimage_in_calldata = 4 * NUM_REGISTERS + ts_run_len(NUM_REGISTERS + 1) + cap * db;
    // Static walk of the stream (the runtime walk in decode_calldata must end at the same
    // offsets).
    let widths: Vec<usize> = (0..circuit.layers.len())
        .rev()
        .map(|l| {
            if l > 0 {
                circuit.layers[l]
                    .intermediate_layer_width
                    .expect("inner layer width")
            } else {
                num_mem + num_wit + num_setup
            }
        })
        .collect();
    assert!(widths.iter().all(|w| *w < 1 << 16) && widths.len() <= 16);
    // (element count, is a factored-round run): a factored-round run of k (b, c) pairs keeps one
    // image slot (its bit offset); an FE run keeps its lanes, two per word.
    let mut runs: Vec<(usize, bool)> = vec![(GKR_OUTPUTS << e, false)];
    for k in e..t {
        runs.push((2 * k, true));
        runs.push((2 * GKR_OUTPUTS, false));
    }
    for w in &widths {
        runs.push((2 * t, true));
        runs.push((*w, false));
    }
    let calldata_bytes =
        preimage_in_calldata + 8 + runs.iter().map(|(n, _)| fe_run_len(*n)).sum::<usize>() + 8;
    let image_bytes = preimage_in_image
        + 8
        + runs
            .iter()
            .map(|&(n, factored)| {
                if factored {
                    FACTORED_ROUND_SLOT_BYTES
                } else {
                    (n >> 1) * 32 + 16 * (n & 1)
                }
            })
            .sum::<usize>()
        + 8;
    // decode_run handles an odd element count only if some FE run has one.
    let odd_runs = runs.iter().any(|&(n, factored)| !factored && n & 1 == 1);
    let odd_tail = if odd_runs {
        "            if and(n, 1) {
                mstore(dst, shl(128, and(shr(sub(133, and(bit, 7)), calldataload(add(cd, shr(3, bit)))), FE_MASK)))
                bit := add(bit, FE_BITS)
            }
"
    } else {
        ""
    };
    // one 256-bit word, layer i in bits [16i, 16i + 16)
    let widths_word: String = widths.iter().rev().map(|w| format!("{w:04x}")).collect();
    let body = format!(
        "            let cd := {preimage_in_calldata}
            let image := {preimage_in_image}
            calldatacopy(add({IMAGE_PTR}, image), cd, 8) // external PoW nonce
            cd, image := decode_next_run(add(cd, 8), add(image, 8), {outputs})
            for {{ let k := {e} }} lt(k, {t}) {{ k := add(k, 1) }} {{
                cd, image := record_factored_run(cd, image, k)
                cd, image := decode_next_run(cd, image, {lines})
            }}
            // circuit layers, top first; at-point eval counts 16 bits each
            for {{ let l := 0 }} lt(l, {layers}) {{ l := add(l, 1) }} {{
                cd, image := record_factored_run(cd, image, {t})
                cd, image := decode_next_run(cd, image, and(shr(mul(16, l), 0x{widths_word}), 0xffff))
            }}
            calldatacopy(add({IMAGE_PTR}, image), cd, 8) // WHIR batching PoW nonce
            if iszero(and(eq(add(cd, 8), {calldata_bytes}), eq(add(image, 8), {image_bytes}))) {{ revert(0, 0) }}
",
        outputs = GKR_OUTPUTS << e,
        lines = 2 * GKR_OUTPUTS,
        layers = widths.len(),
    );

    let setup_cap_image: Vec<u8> = setup_cap
        .iter()
        .flat_map(|d| d.iter().flat_map(|w| w.to_le_bytes()))
        .collect();
    let setup_cap_in_image = 12 * NUM_REGISTERS + 12 + 4 * num_top_bits;
    let setup_cap_len = setup_cap_image.len();
    let pc_le = u32::from_le_bytes(final_pc.to_be_bytes());
    let ts_off = 4 * NUM_REGISTERS;
    let top_off = ts_off + ts_run_len(NUM_REGISTERS + 1);
    let cap_off = top_off;
    // the pinned top bits as preimage LE u32s, left-aligned in one word
    let mut top_word = [0u8; 32];
    for (slot, tb) in top_word.chunks_mut(4).zip(top_bits) {
        slot.copy_from_slice(&tb.to_le_bytes());
    }
    let top_word: String = top_word.iter().map(|b| format!("{b:02x}")).collect();
    let ts_pad = (8 - (38 * (NUM_REGISTERS + 1)) % 8) % 8;
    let yul = format!(
        "
        // ── Calldata decoder: the GKR half's only calldata reader. Writes the decoded GKR image
        // at IMAGE_PTR(); the GKR half reads that image at image offsets, the WHIR half reads its
        // stream from calldata after the GKR section.
        // FE-run(n) at cd: element j = bits [123j, 123j + 123) MSB-first, the pad bits of the last
        // byte zero. Elements 2i, 2i + 1 lie in the word loaded at byte bit >> 3 (bit & 7 ≤ 7,
        // 7 + 246 ≤ 256) and go to the two BE16 lanes at dst + 32i. No range check here: the
        // verifier checks every lane of these runs < P where it reads it (output evaluations, LSB
        // lines, at-point evaluations).
        function fe_pair_lanes(x) -> w {{
            w := or(shl(128, and(shr(FE_BITS, x), FE_MASK)), and(x, FE_MASK))
        }}
        function decode_run(cd, n, dst) {{
            // four pairs = 984 bits = 123 bytes: pair k at byte (246k) >> 3, shifted by 10 − (246k & 7)
            for {{ let end := add(cd, mul(123, shr(3, n))) }} lt(cd, end) {{ cd := add(cd, 123) }} {{
                mstore(dst, fe_pair_lanes(shr(10, calldataload(cd))))
                mstore(add(dst, 32), fe_pair_lanes(shr(4, calldataload(add(cd, 30)))))
                mstore(add(dst, 64), fe_pair_lanes(shr(6, calldataload(add(cd, 61)))))
                mstore(add(dst, 96), fe_pair_lanes(shr(8, calldataload(add(cd, 92)))))
                dst := add(dst, 128)
            }}
            let bit := 0
            for {{ let end := mul(246, and(shr(1, n), 3)) }} lt(bit, end) {{ bit := add(bit, 246) }} {{
                mstore(dst, fe_pair_lanes(shr(sub(10, and(bit, 7)), calldataload(add(cd, shr(3, bit))))))
                dst := add(dst, 32)
            }}
{odd_tail}            check_run_pad(cd, bit)
        }}
        // The pad bits after `bits` run bits at cd must be zero.
        function check_run_pad(cd, bits) {{
            let pad := and(sub(0, bits), 7)
            if and(byte(0, calldataload(add(cd, shr(3, sub(add(bits, pad), 1))))), sub(shl(pad, 1), 1)) {{ revert(0, 0) }}
        }}
        // decode_run over the run at (cd, image): the next calldata and image offsets.
        function decode_next_run(cd, image, n) -> next_cd, next_image {{
            decode_run(cd, n, add({IMAGE_PTR}, image))
            next_cd := add(cd, shr(3, add(mul(FE_BITS, n), 7)))
            next_image := add(image, shl(4, n))
        }}
        // Factored-round run of k (b, c) pairs: the round functions read the pairs from calldata
        // (cd_load) and range-check them; the run's single image slot holds its bit offset. The
        // decoder shares run_end and cd_digest with the WHIR half (whir.sol).
        function record_factored_run(cd, image, k) -> next_cd, next_image {{
            mstore(add({IMAGE_PTR}, image), shl(3, cd))
            next_cd := run_end(cd, shl(1, k))
            next_image := add(image, {FACTORED_ROUND_SLOT_BYTES})
        }}
        function cd_load(off) -> w {{
            w := calldataload(off)
        }}
        // A 19-bit limb as the 4 little-endian bytes of its u32, left-aligned.
        function limb19_le(x) -> w {{
            w := or(or(shl(248, and(x, 0xff)), shl(240, and(shr(8, x), 0xff))), shl(232, shr(16, x)))
        }}
        // TS-run pair i: bits [38i, 38i + 38) = low19 ‖ high19.
        function cd_timestamp(i) -> lo, hi {{
            let bit := mul(38, i)
            let x := and(shr(sub(218, and(bit, 7)), calldataload(add({ts_off}, shr(3, bit)))), 0x3fffffffff)
            lo := shr(19, x)
            hi := and(x, 0x7ffff)
        }}
        // Byte-reverse each u32 lane of a 32-byte word (BE digest words → preimage LE words).
        function bswap32x8(w) -> r {{
            r := or(shr(8, and(w, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00)),
                    shl(8, and(w, 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff)))
            r := or(shr(16, and(r, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000)),
                    shl(16, and(r, 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff)))
        }}
        function decode_calldata() {{
            // preimage: registers (value, ts_low, ts_high) as LE u32
            for {{ let i := 0 }} lt(i, {NUM_REGISTERS}) {{ i := add(i, 1) }} {{
                let dst := add({IMAGE_PTR}, mul(12, i))
                calldatacopy(dst, mul(4, i), 4)
                let lo, hi := cd_timestamp(i)
                mstore(add(dst, 4), limb19_le(lo))
                mstore(add(dst, 8), limb19_le(hi))
            }}
            {{
                let lo, hi := cd_timestamp({NUM_REGISTERS})
                mstore(add({IMAGE_PTR}, {pc_off}), shl(224, {pc_le:#x})) // pinned final PC
                mstore(add({IMAGE_PTR}, {fts_lo}), limb19_le(lo))
                mstore(add({IMAGE_PTR}, {fts_hi}), limb19_le(hi))
            }}
            if and(byte(0, calldataload({ts_last})), {ts_pad_mask:#x}) {{ revert(0, 0) }}
            // pinned inits/teardowns top bits (the setup cap below overwrites the rest of the word)
            mstore(add({IMAGE_PTR}, {top_image}), 0x{top_word})
            // pinned setup cap
            codecopy(add({IMAGE_PTR}, {setup_cap_in_image}), add(mload(SETUP_CODE_OFFSET_PTR), __TEMPLATE_DATA_CAP_OFFSET), {setup_cap_len})
            // memory cap: {cap} DIGESTs of {db} bytes, as preimage LE words and as the WHIR
            // half's BE base-oracle cap
            for {{ let i := 0 }} lt(i, {cap}) {{ i := add(i, 1) }} {{
                let d := cd_digest(add({cap_off}, mul({db}, i)))
                mstore(add({IMAGE_PTR}, add({mem_cap_in_image}, mul(32, i))), bswap32x8(d))
                mstore(add(__TEMPLATE_WHIR_BCAP0_PTR, mul(32, i)), d)
            }}
{body}        }}
",
        pc_off = 12 * NUM_REGISTERS,
        fts_lo = 12 * NUM_REGISTERS + 4,
        fts_hi = 12 * NUM_REGISTERS + 8,
        ts_last = top_off - 1,
        ts_pad_mask = (1u32 << ts_pad) - 1,
        top_image = 12 * NUM_REGISTERS + 12,
        mem_cap_in_image = 12 * NUM_REGISTERS + 12 + 4 * num_top_bits + 32 * cap,
    );
    GkrDecoder {
        yul,
        setup_cap_image,
        image_bytes,
        calldata_bytes,
    }
}
