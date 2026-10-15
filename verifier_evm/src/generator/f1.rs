//! F1 GKR verifier pieces: the generated calldata decoder (the only calldata reader of the
//! F1 GKR verifier), which writes the v0 GKR calldata image into memory, and the rewrite of
//! every other calldata access into a read of that image.

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;

use crate::encoding::{fe_run_len, ts_run_len, FormatParams};

/// Memory address of the v0 calldata image, as the Yul expression the rewritten readers use.
pub(crate) const V0_PTR: &str = "F1_V0_PTR()";

/// GKR output lines (5 output types × [read/num, write/den]).
const GKR_OUTPUTS: usize = 10;
const NUM_REGISTERS: usize = 32;

/// The decoder's layout: every F1 run in stream order with its v0 destination.
pub(crate) struct GkrDecoder {
    pub yul: String,
    /// Length of the v0 GKR calldata image.
    pub v0_bytes: usize,
}

/// `calldataload(x)` → `mload(add(V0, x))`, `calldatacopy(d, x, n)` → `mcopy(d, add(V0, x), n)`,
/// `calldatasize()` → the v0 length. Panics on any other calldata opcode.
pub(crate) fn calldata_to_v0_memory(src: &str, v0_bytes: usize) -> String {
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
            // inside a longer identifier, e.g. `gate_calldataload`
            out.push_str("calldata");
            rest = &tail["calldata".len()..];
        } else if let Some(after) = tail.strip_prefix("calldatasize()") {
            out.push_str(&v0_bytes.to_string());
            rest = after;
        } else if let Some(op) = ["calldataload", "calldatacopy"]
            .into_iter()
            .find(|op| tail.starts_with(&format!("{op}(")))
        {
            let open = op.len();
            let end = close(tail, open);
            let args = calldata_to_v0_memory(&tail[open + 1..end], v0_bytes);
            if op == "calldataload" {
                out.push_str(&format!("mload(add({V0_PTR}, {}))", args.trim()));
            } else {
                let commas = top_level_commas(&args);
                assert_eq!(commas.len(), 2, "calldatacopy takes three arguments");
                let (dst, off, len) = (
                    &args[..commas[0]],
                    &args[commas[0] + 1..commas[1]],
                    &args[commas[1] + 1..],
                );
                out.push_str(&format!(
                    "mcopy({}, add({V0_PTR}, {}), {})",
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

/// 32-byte `[u32; 8]` digest words as the preimage stores them: each word little-endian.
fn le_words_literal(d: &[u32; 8]) -> String {
    let bytes: Vec<u8> = d.iter().flat_map(|w| w.to_le_bytes()).collect();
    format!(
        "0x{}",
        bytes.iter().map(|b| format!("{b:02x}")).collect::<String>()
    )
}

/// The decoder for `circuit` under `params`: `f1_decode()` reads the whole F1 GKR section,
/// checks every run (`v < P`, zero padding) and the section length, and writes the v0 GKR
/// calldata image at [`V0_PTR`].
pub(crate) fn gkr_decoder(
    circuit: &GKRCircuitArtifact<Proth120>,
    params: &FormatParams,
    final_pc: u32,
    setup_cap: &[[u32; 8]],
    num_top_bits: usize,
) -> GkrDecoder {
    let cap = params.cap();
    let db = params.digest_bytes;
    assert_eq!(setup_cap.len(), cap, "setup cap size");
    let t = params.trace_log2;
    let e = params.explicit_output_log2;
    let num_mem = circuit.memory_layout.total_width;
    let num_wit = circuit.witness_layout.total_width;
    let num_setup = circuit.generic_lookup_tables_width;

    // (F1 runs) — the preimage region is decoded by f1_preimage; the rest is runs and raw bytes
    let preimage_v0 = 12 * NUM_REGISTERS + 12 + 4 * num_top_bits + 2 * 32 * cap;
    let preimage_f1 =
        4 * NUM_REGISTERS + ts_run_len(NUM_REGISTERS + 1) + 4 * num_top_bits + cap * db;
    // Static walk of the stream (the runtime walk in f1_decode must end at the same offsets).
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
    let mut runs: Vec<(usize, usize)> = vec![(GKR_OUTPUTS << e, 32)];
    for k in e..t {
        runs.push((2 * k, 64)); // E1 round slots: (b, c) at the v0 slot of (c0..c3)
        runs.push((2 * GKR_OUTPUTS, 32));
    }
    for w in &widths {
        runs.push((2 * t, 64));
        runs.push((*w, 32));
    }
    let f1 = preimage_f1 + 8 + runs.iter().map(|(n, _)| fe_run_len(*n)).sum::<usize>() + 8;
    let v0 = preimage_v0
        + 8
        + runs
            .iter()
            .map(|(n, stride)| (n >> 1) * stride + 16 * (n & 1))
            .sum::<usize>()
        + 8;
    // one 256-bit word, layer i in bits [16i, 16i + 16)
    let widths_word: String = widths.iter().rev().map(|w| format!("{w:04x}")).collect();
    let body = format!(
        "            let cd := {preimage_f1}
            let v0 := {preimage_v0}
            calldatacopy(add({V0_PTR}, v0), cd, 8) // external PoW nonce
            cd, v0 := f1_seq(add(cd, 8), add(v0, 8), {outputs}, 32)
            for {{ let k := {e} }} lt(k, {t}) {{ k := add(k, 1) }} {{
                cd, v0 := f1_seq(cd, v0, mul(2, k), 64)
                cd, v0 := f1_seq(cd, v0, {lines}, 32)
            }}
            // circuit layers, top first; at-point eval counts 16 bits each
            for {{ let l := 0 }} lt(l, {layers}) {{ l := add(l, 1) }} {{
                cd, v0 := f1_seq(cd, v0, {rounds2}, 64)
                cd, v0 := f1_seq(cd, v0, and(shr(mul(16, l), 0x{widths_word}), 0xffff), 32)
            }}
            calldatacopy(add({V0_PTR}, v0), cd, 8) // WHIR batching PoW nonce
            if iszero(and(eq(add(cd, 8), {f1}), eq(add(v0, 8), {v0}))) {{ revert(0, 0) }}
",
        outputs = GKR_OUTPUTS << e,
        lines = 2 * GKR_OUTPUTS,
        layers = widths.len(),
        rounds2 = 2 * t,
    );

    let setup_cap_stores: String = setup_cap
        .iter()
        .enumerate()
        .map(|(i, d)| {
            format!(
                "            mstore(add({V0_PTR}, {}), {})\n",
                12 * NUM_REGISTERS + 12 + 4 * num_top_bits + 32 * i,
                le_words_literal(d)
            )
        })
        .collect();
    let digest_mask = if db == 32 {
        "w".to_string()
    } else {
        format!("and(w, not(sub(shl({}, 1), 1)))", 8 * (32 - db))
    };
    let pc_le = u32::from_le_bytes(final_pc.to_be_bytes());
    let ts_off = 4 * NUM_REGISTERS;
    let top_off = ts_off + ts_run_len(NUM_REGISTERS + 1);
    let cap_off = top_off + 4 * num_top_bits;
    let ts_pad = (8 - (38 * (NUM_REGISTERS + 1)) % 8) % 8;
    let yul = format!(
        "
        // ── F1 decoder: the only calldata reader. Writes the v0 GKR calldata image at
        // F1_V0_PTR(); the verifier below reads that image at v0 offsets.
        // FE-run(n) at cd: element j = bits [123j, 123j + 123) MSB-first, canonical (< P), the
        // pad bits of the last byte zero. Elements 2i, 2i + 1 go to the two lanes of the word at
        // dst + i·pair_stride; both lie in the word loaded at byte bit >> 3 (bit & 7 ≤ 7, 7 + 246 ≤ 256).
        function f1_run(cd, n, dst, pair_stride) {{
            let Pm := mload(P_PTR)
            let bit := 0
            for {{ let end := mul(246, shr(1, n)) }} lt(bit, end) {{ bit := add(bit, 246) }} {{
                let x := shr(sub(10, and(bit, 7)), calldataload(add(cd, shr(3, bit))))
                let a := and(shr(123, x), 0x7ffffffffffffffffffffffffffffff)
                let b := and(x, 0x7ffffffffffffffffffffffffffffff)
                if iszero(and(lt(a, Pm), lt(b, Pm))) {{ revert(0, 0) }}
                mstore(dst, or(shl(128, a), b))
                dst := add(dst, pair_stride)
            }}
            if and(n, 1) {{
                let a := and(shr(sub(133, and(bit, 7)), calldataload(add(cd, shr(3, bit)))), 0x7ffffffffffffffffffffffffffffff)
                if iszero(lt(a, Pm)) {{ revert(0, 0) }}
                mstore(dst, shl(128, a))
                bit := add(bit, 123)
            }}
            let pad := and(sub(0, bit), 7)
            if and(byte(0, calldataload(add(cd, shr(3, sub(add(bit, pad), 1))))), sub(shl(pad, 1), 1)) {{ revert(0, 0) }}
        }}
        // f1_run over the run at (cd, v0): the next F1 and v0 offsets.
        function f1_seq(cd, v0, n, pair_stride) -> next_cd, next_v0 {{
            f1_run(cd, n, add({V0_PTR}, v0), pair_stride)
            next_cd := add(cd, shr(3, add(mul(123, n), 7)))
            next_v0 := add(v0, add(mul(shr(1, n), pair_stride), shl(4, and(n, 1))))
        }}
        // A 19-bit limb as the 4 little-endian bytes of its u32, left-aligned.
        function f1_le19(x) -> w {{
            w := or(or(shl(248, and(x, 0xff)), shl(240, and(shr(8, x), 0xff))), shl(232, shr(16, x)))
        }}
        // TS-run pair i: bits [38i, 38i + 38) = low19 ‖ high19.
        function f1_ts(i) -> lo, hi {{
            let bit := mul(38, i)
            let x := and(shr(sub(218, and(bit, 7)), calldataload(add({ts_off}, shr(3, bit)))), 0x3fffffffff)
            lo := shr(19, x)
            hi := and(x, 0x7ffff)
        }}
        // Byte-reverse each u32 lane of a 32-byte word (BE digest words → preimage LE words).
        function f1_bswap32x8(w) -> r {{
            r := or(shr(8, and(w, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00)),
                    shl(8, and(w, 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff)))
            r := or(shr(16, and(r, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000)),
                    shl(16, and(r, 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff)))
        }}
        function f1_decode() {{
            if iszero(eq(calldatasize(), {f1})) {{ revert(0, 0) }}
            // preimage: registers (value, ts_low, ts_high) as LE u32
            for {{ let i := 0 }} lt(i, {NUM_REGISTERS}) {{ i := add(i, 1) }} {{
                let dst := add({V0_PTR}, mul(12, i))
                calldatacopy(dst, mul(4, i), 4)
                let lo, hi := f1_ts(i)
                mstore(add(dst, 4), f1_le19(lo))
                mstore(add(dst, 8), f1_le19(hi))
            }}
            {{
                let lo, hi := f1_ts({NUM_REGISTERS})
                mstore(add({V0_PTR}, {pc_off}), shl(224, {pc_le:#x})) // pinned final PC
                mstore(add({V0_PTR}, {fts_lo}), f1_le19(lo))
                mstore(add({V0_PTR}, {fts_hi}), f1_le19(hi))
            }}
            if and(byte(0, calldataload({ts_last})), {ts_pad_mask:#x}) {{ revert(0, 0) }}
            calldatacopy(add({V0_PTR}, {top_v0}), {top_off}, {top_len})
            // pinned setup cap
{setup_cap_stores}            // memory cap: {cap} DIGESTs of {db} bytes
            for {{ let i := 0 }} lt(i, {cap}) {{ i := add(i, 1) }} {{
                let w := calldataload(add({cap_off}, mul({db}, i)))
                mstore(add({V0_PTR}, add({mem_cap_v0}, mul(32, i))), f1_bswap32x8({digest_mask}))
            }}
{body}        }}
",
        pc_off = 12 * NUM_REGISTERS,
        fts_lo = 12 * NUM_REGISTERS + 4,
        fts_hi = 12 * NUM_REGISTERS + 8,
        ts_last = top_off - 1,
        ts_pad_mask = (1u32 << ts_pad) - 1,
        top_v0 = 12 * NUM_REGISTERS + 12,
        top_len = 4 * num_top_bits,
        mem_cap_v0 = 12 * NUM_REGISTERS + 12 + 4 * num_top_bits + 32 * cap,
    );
    GkrDecoder { yul, v0_bytes: v0 }
}
