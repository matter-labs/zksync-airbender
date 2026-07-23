use cs::{
    definitions::{
        gkr::{
            AddressSpaceType, NoFieldLinearRelation, NoFieldSingleColumnLookupRelation,
            NoFieldVectorLookupRelation, RamWordRepresentation,
        },
        GKRAddress::{self, InnerLayer},
        VirtualSetupPoly,
    },
    gkr_compiler::{
        CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
        GKRCircuitArtifact, GKRLayerDescription, GateArtifacts, InitsOrTeardownsTimestampAndValue,
        NoFieldGKRCacheRelation, NoFieldGKRRelation, NoFieldMaxQuadraticGKRRelation,
        NoFieldSpecialMemoryContributionRelation,
    },
};
// use cs::gkr_compiler::NoFieldStructuredExpression;
use field::baby_bear::base::BabyBearField;
use field::Proth120;

/// Proth120 modulus P = 7*2^120 + 1 (same as gkr.sol / whir.sol once migrated).
const PROTH120_P: u128 = 0x7000000000000000000000000000001;

/// Width of the generic lookup tables (each generic lookup is a tuple of this many columns, and
/// the setup carries this many lookup columns). Validated against the artifact's
/// `generic_lookup_tables_width` in `emit_circuit_yul`, then used for every lookup-tuple length
/// check so the magic `10` never appears inline.
const LOOKUP_TABLES_WIDTH: usize = 10;
use field::PrimeField;

trait EachRefRev<T, const N: usize> {
    fn each_ref_rev(&self) -> [&T; N];
    fn each_ref_revmap<U>(&self, f: impl FnMut(&T) -> U) -> [U; N];
}

impl<T, const N: usize> EachRefRev<T, N> for [T; N] {
    fn each_ref_rev(&self) -> [&T; N] {
        std::array::from_fn(|i| &self[N - 1 - i])
    }

    fn each_ref_revmap<U>(&self, mut f: impl FnMut(&T) -> U) -> [U; N] {
        let mut out = self.each_ref_rev().map(|x| f(x));
        out.reverse();
        out
    }
}

struct Yul(String);
struct Dual(String, Yul);
impl std::fmt::Display for Dual {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl std::fmt::LowerHex for Dual {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Display;
        self.1 .0.fmt(f) // yul
    }
}
impl std::fmt::Octal for Dual {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.1.fmt(f)
    }
}
impl std::fmt::LowerExp for Dual {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.1.fmt(f)
    }
}

impl std::fmt::LowerHex for Yul {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.0, f)
    }
}
impl std::fmt::Octal for Yul {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.calldataload_idx(), f)
    }
}
impl std::fmt::LowerExp for Yul {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.mload_idx(), f)
    }
}
macro_rules! yul_format {
    ($($arg:tt)*) => {
        Yul(indoc::formatdoc!($($arg)*).replace('\t', "    "))
    };
}
// Main circuit.yul accumulator. `yul_println!` appends here (unless YUL_BUFFER is Some,
// which defers into a sub-function buffer). `emit_circuit_yul` resets it, runs the emission,
// and drains it into the returned String. `GEN_LOCK` serializes concurrent emit calls so
// parallel tests don't corrupt the shared accumulator.
static YUL_MAIN_OUTPUT: std::sync::OnceLock<std::sync::Mutex<String>> = std::sync::OnceLock::new();
static GEN_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
fn yul_main_output() -> &'static std::sync::Mutex<String> {
    YUL_MAIN_OUTPUT.get_or_init(|| std::sync::Mutex::new(String::new()))
}
// When Some, yul_println! appends here (deferred emission) instead of the main accumulator.
// Used to collect the per-layer gate sub-functions and emit them at TOP LEVEL after the layer.
static YUL_BUFFER: std::sync::OnceLock<std::sync::Mutex<Option<String>>> =
    std::sync::OnceLock::new();
// When Some, the cache loop's InnerLayer-address resolver records the referenced offset here.
// These are the "extra" (cache-dependency) inputs — the ones the transcript absorbs AFTER the
// batching draw — as opposed to the gate inputs (final_step) absorbed before it.
static CACHE_DEP_OFFSETS: std::sync::OnceLock<std::sync::Mutex<Option<Vec<usize>>>> =
    std::sync::OnceLock::new();
macro_rules! yul_println {
    ($($arg:tt)*) => {
        {
            let yul = yul_format!($($arg)*).0;
            let buf = YUL_BUFFER.get_or_init(|| std::sync::Mutex::new(None));
            let mut b = buf.lock().unwrap();
            if let Some(s) = b.as_mut() {
                s.push_str(&yul);
                s.push('\n');
            } else {
                let mut out = yul_main_output().lock().unwrap();
                out.push_str(&yul);
                out.push('\n');
            }
        }
    };
}
impl Yul {
    fn calldataload(idx: &usize) -> Self {
        // While the cache loop is active, every calldata read is a cache dependency (a transcript
        // "extra"): record its calldata offset. Inactive elsewhere (gates/sumcheck) → no-op.
        if let Some(v) = CACHE_DEP_OFFSETS
            .get_or_init(|| std::sync::Mutex::new(None))
            .lock()
            .unwrap()
            .as_mut()
        {
            v.push(*idx);
        }
        // The circuit-layer calldata cursor lives in a fixed heap slot (CIRCUIT_PTR), not a
        // function parameter, so the gate/cache/chunk sub-functions need not carry `ptr` —
        // that param was the single deepest slot pushing each of them 1 over the EVM limit.
        yul_format!("shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, {idx}))))")
    }
    fn mload(idx: &usize) -> Self {
        yul_format!("mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, {idx})))")
    }
    fn calldataload_idx(&self) -> usize {
        let s = self.0.trim();
        let prefix = "shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, ";
        let suffix = "))))";
        let idx = s
            .strip_prefix(prefix)
            .and_then(|s| s.strip_suffix(suffix))
            .unwrap_or_else(|| panic!("expected simple calldata load, got: {s}"));
        assert!(
            idx.chars().all(|c| c.is_ascii_digit()),
            "expected literal calldata index, got: {idx}"
        );
        idx.parse().unwrap()
    }
    fn mload_idx(&self) -> usize {
        let s = self.0.trim();
        let prefix = "mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, ";
        let suffix = ")))";
        let idx = s
            .strip_prefix(prefix)
            .and_then(|s| s.strip_suffix(suffix))
            .unwrap_or_else(|| panic!("expected simple cache load, got: {s}"));
        assert!(
            idx.chars().all(|c| c.is_ascii_digit()),
            "expected literal cache index, got: {idx}"
        );
        idx.parse().unwrap()
    }
    fn mstore(idx: &usize) -> Self {
        yul_format!("mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, {idx})), mod(gate, P))")
        // mod to prevent overflows with pointcheck const-cache multiplications
    }
    fn logup_gamma() -> Self {
        yul_format!("mload(add(LOGUP_CHALLS_PTR(), 32))")
    }
    fn logup_alpha() -> Self {
        yul_format!("mload(LOGUP_CHALLS_PTR())")
    }
    fn memory_gamma() -> Self {
        yul_format!("mload(add(MEMORY_CHALLS_PTR(), mul(32, 6)))")
    }
    fn memory_alpha(idx: usize) -> Self {
        match idx {
            0..6 => yul_format!("mload(add(MEMORY_CHALLS_PTR(), mul(32, {idx})))"),
            _ => unreachable!("we do not have memory linearisation challenge alpha_{idx}"),
        }
    }
}
fn superscript(idx: usize) -> String {
    idx.to_string()
        .chars()
        .map(|c| match c {
            '0' => '⁰',
            '1' => '¹',
            '2' => '²',
            '3' => '³',
            '4' => '⁴',
            '5' => '⁵',
            '6' => '⁶',
            '7' => '⁷',
            '8' => '⁸',
            '9' => '⁹',
            _ => unreachable!(),
        })
        .collect()
}
fn const_to_evm(c: &u32) -> Dual {
    assert!(
        *c < BabyBearField::ORDER,
        "we don't expect circuits with unreduced constants"
    );
    // first check if negative
    let (sign, modc, yul) = if *c > BabyBearField::ORDER / 2 {
        let modc = BabyBearField::ORDER - c;
        ("-", modc, yul_format!("sub(P, {modc})"))
    } else {
        ("", *c, yul_format!("{c}"))
    };
    let normal = match modc {
        modc if modc.is_power_of_two() && !(0..=2).contains(&modc) => {
            let power = modc.trailing_zeros();
            format!("{sign}2^{power}")
        }
        _ => format!("{sign}{modc}"),
    };
    Dual(normal, yul)
}
fn u128_to_neg(Dual(input, yul): &Dual) -> Dual {
    Dual(format!("-{input}"), yul_format!("sub(mul(2, P), {yul:x})"))
}

/// Proth120-aware constant emitter (replaces `const_to_evm` for the Proth120 target).
/// Field elements are < P < 2^123 (one uint128). Emit small positives as literals,
/// small negatives (near P) as `sub(P, n)`, and anything else as a full 128-bit literal.
/// The Yul consumer must funnel every product through `mulmod` before adding to a
/// reduced value (non-canonical arithmetic, per HEURISTICS.md).
#[allow(dead_code)]
fn proth120_const_to_evm(c: &Proth120) -> Dual {
    let v = c.to_u128();
    if v == 0 {
        return Dual("0".to_string(), yul_format!("0"));
    }
    if v < (1u128 << 32) {
        let normal = if v.is_power_of_two() && v > 2 {
            format!("2^{}", v.trailing_zeros())
        } else {
            format!("{v}")
        };
        return Dual(normal, yul_format!("{v}"));
    }
    let neg = PROTH120_P - v;
    if neg < (1u128 << 32) {
        let normal = if neg.is_power_of_two() && neg > 2 {
            format!("-2^{}", neg.trailing_zeros())
        } else {
            format!("-{neg}")
        };
        return Dual(normal, yul_format!("sub(P, {neg})"));
    }
    // Genuine mid-range coefficient: emit the full canonical value as a hex literal.
    Dual(format!("0x{v:x}"), yul_format!("0x{v:x}"))
}

/// Emit a small non-negative integer constant (memory address / offset / timestamp offset)
/// as a Proth120 field literal. These are genuine small integers (< 2^32), never field-negative.
#[allow(dead_code)]
fn u32_lit(c: u32) -> Dual {
    Dual(format!("{c}"), yul_format!("{c}"))
}

/// Emit a `coeff · input` term into a gate/cache's non-canonical `add`-chain.
///
/// The generic form is `mulmod(coeff, input, P)` (product reduced < P). But the legacy
/// Yul optimizer does NOT simplify `mulmod(1, x, P)`, so a coefficient of 1 would compile
/// to a real MULMOD (PUSH 1, reconstruct P, MULMOD ≈ 8 bytes) at every occurrence — 395 of
/// them across layer-0. When the coefficient is exactly 1 we emit the bare `input`.
///
/// This is exact, not an approximation: `input` here is always a single `shr(128, …)`
/// calldata lane (< 2^128). Whether it lands in [0, P) or [P, 2^128) it flows into the
/// surrounding `add`-chain whose result is canonicalized by the gate's trailing `mod(_, P)`
/// (or, for accumulators, the next round's `mulmod(_, alpha, P)`). Sum stays far below
/// 2^256, so the result is bit-identical mod P. The human-readable side is unchanged.
fn scaled(c: &Dual, input: &Dual) -> Dual {
    let display = format!("{c}{input}");
    if c.1 .0 == "1" {
        Dual(display, yul_format!("{input:x}"))
    } else {
        Dual(display, yul_format!("mulmod({c:x}, {input:x}, P)"))
    }
}

/// One collected layer-0 quadratic/linear term for the table-driven evaluator.
/// `coeff` is canonical in [0, P); `b == None` marks a linear term (`coeff·col[a]`),
/// `b == Some` a quadratic term (`coeff·col[a]·col[b]`). `slot` is the gate's index into
/// the GATEVAL accumulator array.
struct QTerm {
    slot: u32,
    a: u32,
    b: Option<u32>,
    coeff: u128,
}

/// Emit the compact, table-driven evaluation of layer-0's max-quadratic gates (size opt).
///
/// Instead of ~20 KB of unrolled per-term `mulmod` code, every term becomes a packed record and
/// a handful of fixed-stride loops sum `coeff · col[a] · col[b]` into `GATEVAL[slot]`; the Horner
/// chunk functions then read each gate's value as `mload(GATEVAL+32·slot)`, so the accumulation
/// order / α-powers / `sccl0` alignment are byte-for-byte unchanged. Records are bucketed by
/// (quadratic|linear, coeff sign, coeff byte-width): small coefficients store just their
/// magnitude (1/2/4 B), small negatives store the magnitude and are negated in-loop as
/// `sub(Pm, mag)`, and genuine mid-range coefficients keep their full 16-byte canonical value.
/// The modulus is loaded once from the `P` constant into the local `Pm` and reused (a cheap DUP
/// in the shallow loop — no per-op PUSH16 and no heap reload). GATEVAL lives in pristine (zero)
/// heap, so only nonzero gate constants need an explicit seed.
/// `gate_constant_terms`: the additive constant of each quadratic relation `(gate slot, value)`,
/// only for gates whose constant is nonzero (it seeds `GATEVAL[slot]` before the term loops add).
fn emit_layer0_quad_table(terms: &[QTerm], gate_constant_terms: &[(u32, u128)]) -> String {
    use std::collections::BTreeMap;
    // canonical coeff -> (byte width, is_negative, stored value). Small +ve: store as-is.
    // Small -ve (canonical near P): store magnitude P-v, negate in-loop. Else: full 16 B.
    fn classify(v: u128) -> (usize, bool, u128) {
        let width_of = |x: u128| {
            if x <= 0xff {
                1
            } else if x <= 0xffff {
                2
            } else {
                4
            }
        };
        if v < (1u128 << 32) {
            (width_of(v), false, v)
        } else if (PROTH120_P - v) < (1u128 << 32) {
            let m = PROTH120_P - v;
            (width_of(m), true, m)
        } else {
            (16, false, v)
        }
    }
    // bucket key (is_quad, is_neg, width) -> packed record bytes
    let mut buckets: BTreeMap<(bool, bool, usize), Vec<u8>> = BTreeMap::new();
    for t in terms {
        let (width, neg, stored) = classify(t.coeff);
        let is_quad = t.b.is_some();
        let rec = buckets.entry((is_quad, neg, width)).or_default();
        rec.push(t.slot as u8);
        rec.push(t.a as u8);
        if let Some(b) = t.b {
            rec.push(b as u8);
        }
        rec.extend_from_slice(&stored.to_be_bytes()[16 - width..]); // `width` low bytes, big-endian
    }
    // concatenate buckets into one byte stream; record (key, start, count, stride)
    let mut stream: Vec<u8> = vec![];
    let mut layout: Vec<((bool, bool, usize), usize, usize, usize)> = vec![];
    for (key, bytes) in &buckets {
        let (is_quad, _neg, width) = *key;
        let stride = if is_quad { 3 } else { 2 } + width;
        layout.push((*key, stream.len(), bytes.len() / stride, stride));
        stream.extend_from_slice(bytes);
    }
    while stream.len() % 32 != 0 {
        stream.push(0); // pad: the loop mload reads 32 B; trailing bytes are never consumed
    }

    let mut out = String::new();
    out.push_str(
"            // ── layer-0 max-quadratic gates: table-driven evaluation ──────────────────────
            // Each gate's value is Σ(constant + Σ coeff·col[a] + Σ coeff·col[a]·col[b]), summed
            // into gateval[gate_slot] and read back by the Horner chunk functions. Terms are stored
            // as packed records rather than unrolled code (a large bytecode saving). Record layout
            // (big-endian): [gate_slot:1][col_a:1]([col_b:1] for quadratic)[coeff:1|2|4|16]. Records
            // are grouped into buckets by (linear/quadratic, coeff sign, coeff byte-width) so each
            // loop below has one fixed stride; small negative coefficients store their magnitude and
            // are negated in-loop.\n",
    );
    // 1. seed each quadratic relation's nonzero constant term (gateval is pristine zero otherwise)
    if !gate_constant_terms.is_empty() {
        out.push_str(
            "            // seed gateval[gate_slot] with each relation's nonzero constant term\n",
        );
        for (slot, constant_value) in gate_constant_terms {
            out.push_str(&format!(
                "            mstore(add(GKR_GATEVAL_PTR(), mul(32, {slot})), 0x{constant_value:x})\n"
            ));
        }
    }
    // 2. materialize the packed record stream via mstore immediates
    out.push_str("            // packed term records, written 32 bytes at a time\n");
    for (i, chunk) in stream.chunks(32).enumerate() {
        let mut word = [0u8; 32];
        word[..chunk.len()].copy_from_slice(chunk);
        let hex: String = word.iter().map(|b| format!("{b:02x}")).collect();
        out.push_str(&format!(
            "            mstore(add(GKR_QTABLE_PTR(), {}), 0x{hex})\n",
            i * 32
        ));
    }
    // 3. bucket loops — modulus loaded once from the P constant into a local (cheap DUP in the
    //    shallow loop, no per-op PUSH16), calldata + gateval bases hoisted.
    out.push_str(
        "            // accumulate every term into gateval[gate_slot], one loop per bucket\n",
    );
    out.push_str("            {\n");
    out.push_str("            let modulus := P\n");
    out.push_str("            let col_base := mload(CIRCUIT_PTR) // calldata base of the column at-point evals\n");
    out.push_str("            let gateval := GKR_GATEVAL_PTR()\n");
    for (key, start, count, stride) in &layout {
        if *count == 0 {
            continue;
        }
        let (is_quad, neg, width) = *key;
        let off = if is_quad { 3 } else { 2 };
        let shift = 8 * (32 - off - width);
        let mask = match width {
            1 => "0xff".to_string(),
            2 => "0xffff".to_string(),
            4 => "0xffffffff".to_string(),
            _ => "MASK".to_string(),
        };
        let coeff_raw = format!("and(shr({shift}, rec), {mask})");
        let coeff = if neg {
            format!("sub(modulus, {coeff_raw})")
        } else {
            coeff_raw
        };
        let col_a = "shr(128, calldataload(add(col_base, mul(16, byte(1, rec)))))";
        let value = if is_quad {
            let col_b = "shr(128, calldataload(add(col_base, mul(16, byte(2, rec)))))";
            format!("mulmod({col_a}, {col_b}, modulus)")
        } else {
            col_a.to_string()
        };
        let kind = if is_quad { "quadratic" } else { "linear   " };
        let sign = if width == 16 {
            "canonical"
        } else if neg {
            "negative "
        } else {
            "positive "
        };
        let label = format!("{kind} terms, coeff {width:2}B {sign} ({count} records)");
        out.push_str(&format!(
            "            // {label}\n\
             \x20           {{ let rec_ptr := add(GKR_QTABLE_PTR(), {start}) let rec_end := add(rec_ptr, {})\n\
             \x20           for {{ }} lt(rec_ptr, rec_end) {{ rec_ptr := add(rec_ptr, {stride}) }} {{\n\
             \x20               let rec := mload(rec_ptr)\n\
             \x20               let gate_ptr := add(gateval, mul(32, byte(0, rec)))\n\
             \x20               mstore(gate_ptr, addmod(mload(gate_ptr), mulmod({coeff}, {value}, modulus), modulus))\n\
             \x20           }} }}\n",
            count * stride
        ));
    }
    out.push_str("            }\n");
    out
}

/// Emit the Horner accumulation of a contiguous run of quadratic gates (GATEVAL slots `lo..hi`)
/// as a single loop instead of `hi-lo` unrolled `acc := acc·α + mload(GATEVAL+slot)` steps.
/// The gates got consecutive slots in processing order, so a run maps to a consecutive slot
/// range and the loop reproduces the exact Horner order. Emitted inside a chunk function where
/// `acc`/`alpha` are in scope; the modulus is hoisted into a local (loaded once) so the per-
/// iteration `mulmod` uses a cheap stack DUP rather than re-reading P_PTR.
fn quad_run_loop(lo: u32, hi: u32) -> String {
    format!(
        "            {{ let modulus := mload(P_PTR) let gv := GKR_GATEVAL_PTR()\n\
         \x20           for {{ let s := {lo} }} lt(s, {hi}) {{ s := add(s, 1) }} {{\n\
         \x20               acc := add(mulmod(acc, alpha, modulus), mload(add(gv, mul(32, s))))\n\
         \x20           }} }}\n"
    )
}

/// Fold 10 lookup columns into a β-Horner accumulator using 2-arg `gkr_lookrel_step`
/// calls, so no call boundary materializes more than one column expression at a time.
/// The prior 5-arg `gkr_lookrel_compress_half` forced solc to put all five column
/// expressions on the stack at once, running the enclosing cache/gate function 1 slot
/// too deep (neither legacy nor via_ir could place it). Order reproduces the old
/// nesting exactly — inner(0,c5..c9) then outer(_,c0..c4) is Horner over
/// c9,c8,c7,c6,c5,c4,c3,c2,c1,c0 with step(acc,c) = acc·β + c.
fn lookrel_horner(cols: &[Dual]) -> String {
    // Horner over cols[n-1], …, cols[0]: step(acc, c) = acc·β + c. Length comes from the caller
    // (= the artifact's generic-lookup-tuple width), so this works for any table width.
    let mut expr = "0".to_string();
    for i in (0..cols.len()).rev() {
        expr = format!("gkr_lookrel_step({expr}, {:x})", cols[i]);
    }
    expr
}

/// Join the human-readable sides of a lookup tuple's columns with " + " (the display half of the
/// `lookrel_horner` fold).
fn lookrel_display(cols: &[Dual]) -> String {
    cols.iter()
        .map(|d| d.to_string())
        .collect::<Vec<_>>()
        .join(" + ")
}

/// Memory-tuple (gkr_memrel_compress) emitter — module-level so BOTH the cache loop
/// and the gates loop can call it (layer-0 memory deps -> calldataload(idx)).
fn memrel_to_calldata(
    tuple: &NoFieldSpecialMemoryContributionRelation,
    running_max_group_offsets: &mut (usize, usize, usize, usize),
) -> Dual {
    let (running_max_memvar, _running_max_witvar, _running_max_setupvar, _running_max_cachevar) =
        running_max_group_offsets;
    let NoFieldSpecialMemoryContributionRelation {
        address_space,
        address,
        timestamp,
        value,
        timestamp_offset,
    } = tuple;
    let address_space = match address_space {
        CompiledAddressSpaceRelationStrict::Constant(c) => u32_lit(*c),
        CompiledAddressSpaceRelationStrict::IsRam(idx) => {
            *running_max_memvar = *idx.max(running_max_memvar);
            Dual(format!("[{idx}]"), Yul::calldataload(idx))
        }
        CompiledAddressSpaceRelationStrict::IsRegister(idx) => {
            *running_max_memvar = *idx.max(running_max_memvar);
            let var = Dual(format!("[{idx}]"), Yul::calldataload(idx));
            let negvar = u128_to_neg(&var);
            Dual(format!("(1 + {negvar})"), yul_format!("add(1, {negvar:x})"))
        }
    };
    let [addr_low, addr_high] = match address {
        CompiledAddressStrict::Constant(c) => {
            assert!(*c < (1 << 16), "with {address:?} we expect c < 2^16");
            let c = u32_lit(*c);
            let zero = Dual(format!("0"), yul_format!("0"));
            [c, zero]
        }
        CompiledAddressStrict::ConstantU16(c) => {
            let c = u32_lit(*c as u32);
            let zero = Dual(format!("0"), yul_format!("0"));
            [c, zero]
        }
        CompiledAddressStrict::U16Space(idx) => {
            *running_max_memvar = *idx.max(running_max_memvar);
            let var = Dual(format!("[{idx}]"), Yul::calldataload(idx));
            let zero = Dual(format!("0"), yul_format!("0"));
            [var, zero]
        }
        CompiledAddressStrict::U32Space([low, high]) => {
            *running_max_memvar = *low.max(running_max_memvar);
            *running_max_memvar = *high.max(running_max_memvar);
            let low = Dual(format!("[{low}]"), Yul::calldataload(low));
            let high = Dual(format!("[{high}]"), Yul::calldataload(high));
            [low, high]
        }
        _ => todo!(),
    };
    let [ts_low, ts_high] = match timestamp {
        CompiledMemoryTimestamp::Zero => {
            assert_eq!(
                *timestamp_offset, 0,
                "with {timestamp:?} we expect timestamp_offset == 0"
            );
            let zero1 = Dual(format!("0"), yul_format!("0"));
            let zero2 = Dual(format!("0"), yul_format!("0"));
            [zero1, zero2]
        }
        CompiledMemoryTimestamp::Normal([low, high]) => {
            *running_max_memvar = *low.max(running_max_memvar);
            *running_max_memvar = *high.max(running_max_memvar);
            let timestamp_offset = u32_lit(*timestamp_offset);
            let low = Dual(format!("[{low}]"), Yul::calldataload(low));
            let high = Dual(format!("[{high}]"), Yul::calldataload(high));
            [
                Dual(
                    format!("({timestamp_offset} + {low})"),
                    yul_format!("add({timestamp_offset:x}, {low:x})"),
                ),
                high,
            ]
        }
    };
    let [val_low, val_high] = match value {
        RamWordRepresentation::Zero => {
            let zero1 = Dual(format!("0"), yul_format!("0"));
            let zero2 = Dual(format!("0"), yul_format!("0"));
            [zero1, zero2]
        }
        RamWordRepresentation::U16Limbs([low, high]) => {
            *running_max_memvar = *low.max(running_max_memvar);
            *running_max_memvar = *high.max(running_max_memvar);
            let low = Dual(format!("[{low}]"), Yul::calldataload(low));
            let high = Dual(format!("[{high}]"), Yul::calldataload(high));
            [low, high]
        }
        RamWordRepresentation::U8Limbs([ll, lh, hl, hh]) => {
            *running_max_memvar = *ll.max(running_max_memvar);
            *running_max_memvar = *lh.max(running_max_memvar);
            *running_max_memvar = *hl.max(running_max_memvar);
            *running_max_memvar = *hh.max(running_max_memvar);
            let ll = Dual(format!("[{ll}]"), Yul::calldataload(ll));
            let lh = Dual(format!("[{lh}]"), Yul::calldataload(lh));
            let hl = Dual(format!("[{hl}]"), Yul::calldataload(hl));
            let hh = Dual(format!("[{hh}]"), Yul::calldataload(hh));
            let low = Dual(
                format!("([{ll}] + 2⁸[{lh}])"),
                yul_format!("add({ll:x}, shl(8, {lh:x}))"),
            );
            let high = Dual(
                format!("([{hl}] + 2⁸[{hh}])"),
                yul_format!("add({hl:x}, shl(8, {hh:x}))"),
            );
            [low, high]
        }
    };
    let memory_gamma = Dual(format!("γ"), Yul::memory_gamma());
    let memory_alpha1 = Dual(format!("α"), Yul::memory_alpha(0));
    let memory_alpha2 = Dual(format!("α²"), Yul::memory_alpha(1));
    let memory_alpha3 = Dual(format!("α³"), Yul::memory_alpha(2));
    let memory_alpha4 = Dual(format!("α⁴"), Yul::memory_alpha(3));
    let memory_alpha5 = Dual(format!("α⁵"), Yul::memory_alpha(4));
    let memory_alpha6 = Dual(format!("α⁶"), Yul::memory_alpha(5));
    Dual(
        format!("({memory_gamma} + {address_space} + {memory_alpha1}{addr_low} + {memory_alpha2}{addr_high} + {memory_alpha3}{ts_low} + {memory_alpha4}{ts_high} + {memory_alpha5}{val_low} + {memory_alpha6}{val_high})"),
        yul_format!("add(gkr_memrel_compress_low({address_space:x}, {addr_low:x}, {addr_high:x}), gkr_memrel_compress_high({ts_low:x}, {ts_high:x}, {val_low:x}, {val_high:x}))")
    )
}

/// Emit the circuit-specific `circuit.yul` (the GKR per-layer sumcheck/gate functions) for a
/// given circuit artifact, as a String. This is the only circuit-dependent part of the GKR
/// verifier; `generate_verifiers` inlines it into the hand-written gkr.sol template.
pub fn emit_circuit_yul(circuit: &GKRCircuitArtifact<Proth120>) -> String {
    const DEBUG_ENABLE_DUMMY_CHECKS: bool = false;
    // Harden against a layout with a different generic-lookup table width: the lookup-fold code
    // and the WHIR_NUM_SETUP constant both assume exactly LOOKUP_TABLES_WIDTH setup lookup columns.
    assert_eq!(
        circuit.generic_lookup_tables_width, LOOKUP_TABLES_WIDTH,
        "layout: generic_lookup_tables_width is {}, but this generator is specialized for {LOOKUP_TABLES_WIDTH}",
        circuit.generic_lookup_tables_width
    );
    // Serialize concurrent callers and reset the shared accumulator (the yul_println! macro and
    // the sub-function hoisting write into YUL_MAIN_OUTPUT; not re-entrant across threads).
    let _gen_guard = GEN_LOCK.lock().unwrap();
    yul_main_output().lock().unwrap().clear();
    let circuit_rounds = {
        assert!(circuit.trace_len.is_power_of_two() && circuit.trace_len > 0);
        assert_eq!(
            circuit.trace_len,
            1 << 22,
            "we currently expect gkr_compress to go up to 2^22"
        );
        circuit.trace_len.trailing_zeros()
    };
    let layer0_group_widths = (
        circuit.memory_layout.total_width,
        circuit.witness_layout.total_width,
        circuit.generic_lookup_tables_width,
        circuit.layers[0].cached_relations.len(),
    );
    // let mut previous_input_count = 8;
    let mut previous_input_count = 10; // TEMPORARY: unified adds another product pair for inits/teardowns
    for (i, layer) in circuit.layers.iter().enumerate().rev() {
        let GKRLayerDescription {
            layer,
            gates_with_external_connections,
            cached_relations,
            gates,
            intermediate_layer_width,
        } = layer;
        assert!(*layer == i);
        let gates = if i == circuit.layers.len() - 1 {
            assert!(gates.is_empty());
            gates_with_external_connections
        } else {
            assert!(gates_with_external_connections.is_empty());
            gates
        };

        // println!("{i}:");
        yul_println!("
        function sumcheck_circuit_layer{i}(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {{
            // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
            // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
            claim := sccl{i}(alpha)
            // SUMCHECK ROUNDS
            let eq_scale
            // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
            ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
            
            // POINT CHECK
            let acc := 0"); // Horner accumulator starts at 0 (explicit init: the first chunk reads it)
                            // Wrap this layer's cache computations (MemoryTuple / lookups / virtual-setup) in a
                            // dedicated TOP-LEVEL function so their deep expressions (e.g. the 7-arg
                            // gkr_memrel_compress) don't pile onto the layer function's already-tight stack —
                            // buffer them now, hoist the function after the layer, call it inline.
        *YUL_BUFFER
            .get_or_init(|| std::sync::Mutex::new(None))
            .lock()
            .unwrap() = Some(String::new());
        yul_println!("            function scl{i}_caches() {{");
        // Record the InnerLayer offsets the caches depend on (the transcript "extras").
        *CACHE_DEP_OFFSETS
            .get_or_init(|| std::sync::Mutex::new(None))
            .lock()
            .unwrap() = Some(vec![]);
        let mut running_max_group_offsets = (0, 0, 0, 0);
        let mut running_cachedoutput_counter = 0;
        for (cached_address, cached_relation) in cached_relations {
            let output =
                gkraddress_to_outputvar(cached_address, i, &mut running_cachedoutput_counter);
            // Variant name for comments only. (serde_json::to_value overflows on Proth120 u128 field
            // elements — "number out of range" — so match the variant directly.)
            let relation_name = match cached_relation {
                NoFieldGKRCacheRelation::SingleColumnLookup { .. } => "SingleColumnLookup",
                NoFieldGKRCacheRelation::VectorizedLookup(..) => "VectorizedLookup",
                NoFieldGKRCacheRelation::MemoryTuple(..) => "MemoryTuple",
                NoFieldGKRCacheRelation::VectorizedLookupSetup(..) => "VectorizedLookupSetup",
            };

            fn gkraddress_to_calldata(
                address: &GKRAddress,
                expected_layer: usize,
                layer0_group_widths: (usize, usize, usize, usize),
                running_max_group_offsets: &mut (usize, usize, usize, usize),
            ) -> Dual {
                let (l0_memvars, l0_witvars, _l0_setupvars, l0_cachevars) = layer0_group_widths;
                let (
                    running_max_memvar,
                    running_max_witvar,
                    running_max_setupvar,
                    running_max_cachevar,
                ) = running_max_group_offsets;
                match address {
                    InnerLayer { layer, offset }
                        if *layer == expected_layer && expected_layer > 0 =>
                    {
                        if let Some(v) = CACHE_DEP_OFFSETS
                            .get_or_init(|| std::sync::Mutex::new(None))
                            .lock()
                            .unwrap()
                            .as_mut()
                        {
                            v.push(*offset);
                        }
                        Dual(format!("[{offset}]"), Yul::calldataload(offset))
                    }
                    GKRAddress::BaseLayerMemory(offset) if expected_layer == 0 => {
                        *running_max_memvar = *offset.max(running_max_memvar);
                        let calldata_offset = *offset; // memory is first in calldata
                        if let Some(v) = CACHE_DEP_OFFSETS
                            .get_or_init(|| std::sync::Mutex::new(None))
                            .lock()
                            .unwrap()
                            .as_mut()
                        {
                            v.push(calldata_offset);
                        }
                        Dual(
                            format!("[{calldata_offset}]"),
                            Yul::calldataload(&calldata_offset),
                        )
                    }
                    GKRAddress::BaseLayerWitness(offset) if expected_layer == 0 => {
                        *running_max_witvar = *offset.max(running_max_witvar);
                        let calldata_offset = l0_memvars + offset; // witness is second in calldata
                        if let Some(v) = CACHE_DEP_OFFSETS
                            .get_or_init(|| std::sync::Mutex::new(None))
                            .lock()
                            .unwrap()
                            .as_mut()
                        {
                            v.push(calldata_offset);
                        }
                        Dual(
                            format!("[{calldata_offset}]"),
                            Yul::calldataload(&calldata_offset),
                        )
                    }
                    GKRAddress::Setup(offset) if expected_layer == 0 => {
                        *running_max_setupvar = *offset.max(running_max_setupvar);
                        let calldata_offset = l0_memvars + l0_witvars + offset; // setup is third in calldata
                        if let Some(v) = CACHE_DEP_OFFSETS
                            .get_or_init(|| std::sync::Mutex::new(None))
                            .lock()
                            .unwrap()
                            .as_mut()
                        {
                            v.push(calldata_offset);
                        }
                        Dual(
                            format!("[{calldata_offset}]"),
                            Yul::calldataload(&calldata_offset),
                        )
                    }
                    // Cached (virtual) poly: computed from deps + mstore'd to a heap slot earlier
                    // in this layer's processing; gates mload it. Slots are per-layer (reused).
                    GKRAddress::Cached { layer, offset } if *layer == expected_layer => {
                        *running_max_cachevar = *offset.max(running_max_cachevar);
                        Dual(format!("Cache({offset})"), Yul::mload(offset))
                    }
                    GKRAddress::VirtualSetup(virtual_poly) if expected_layer == 0 => {
                        let cache_idx = l0_cachevars + *virtual_poly as usize;
                        *running_max_cachevar = cache_idx.max(*running_max_cachevar);
                        Dual(format!("Cache({cache_idx})"), Yul::mload(&cache_idx))
                    }
                    _ => todo!("unexpected address {address:?} for layer {expected_layer}"),
                }
            }
            fn gkraddress_to_outputvar(
                address: &GKRAddress,
                expected_layer: usize,
                running_cachedoutput_counter: &mut usize,
            ) -> Dual {
                match address {
                    // Cache output for ANY layer: store the computed cached value to its heap slot
                    // (per-layer offset; slots reused across layers since caches are computed and
                    // consumed within one layer's point-check before the next layer runs).
                    GKRAddress::Cached { layer, offset }
                        if *layer == expected_layer && *running_cachedoutput_counter == *offset =>
                    {
                        *running_cachedoutput_counter += 1;
                        Dual(format!("Cache({offset})"), Yul::mstore(offset))
                    }
                    _ => todo!("unexpected address {address:?} for layer {expected_layer}"),
                }
            }
            // fn linrel_to_calldata(inputs: &NoFieldLinearRelation<BabyBearField>, expected_layer: usize) -> String {
            //     let NoFieldLinearRelation { linear_terms, constant } = inputs;
            //     let linear = linear_terms.iter().map(|(c, addr)| {
            //         let input = gkraddress_to_calldata(addr, expected_layer);
            //         format!("{c}{input}")
            //     }).collect::<Vec<_>>().join(" + ");
            //     format!("({constant} + {linear})")
            // }

            match cached_relation {
                // NoFieldGKRCacheRelation::VectorizedLookup(NoFieldVectorLookupRelation{ columns, lookup_set_index: _}) => {
                //     let term = columns.iter().enumerate().map(|(j, column)| {
                //         let linear = linrel_to_calldata(column, i);
                //         let beta_j = "β".to_string() + &superscript(j);
                //         format!("{beta_j}{linear}")
                //     }).collect::<Vec<_>>().join(" + ");
                //     println!("{relation_name}: {term} = {output}");
                // }
                NoFieldGKRCacheRelation::VectorizedLookupSetup(terms) => {
                    let logup_alpha = Dual("β".to_string(), Yul::logup_alpha());
                    let setup = {
                        assert_eq!(terms.len(), LOOKUP_TABLES_WIDTH, "layout: generic lookup setup tuple has {} columns, expected {LOOKUP_TABLES_WIDTH}", terms.len());
                        let sets: Vec<Dual> = terms
                            .iter()
                            .enumerate()
                            .map(|(j, addr)| {
                                let input = gkraddress_to_calldata(
                                    addr,
                                    i,
                                    layer0_group_widths,
                                    &mut running_max_group_offsets,
                                );
                                let beta_j = logup_alpha.0.clone() + &superscript(j);
                                Dual(format!("{beta_j}{input}"), yul_format!("{input:x}"))
                            })
                            .collect();
                        Dual(
                            lookrel_display(&sets),
                            yul_format!("{}", lookrel_horner(&sets)),
                        )
                    };
                    // println!("{relation_name}: {setup} = {output}");
                    yul_println!(
                        "
                    \t{{  // {relation_name}: {setup} = {output}
                    \t    let gate := {setup:x}
                    \t    {output:x}
                    \t}}"
                    );
                }
                NoFieldGKRCacheRelation::VectorizedLookup(NoFieldVectorLookupRelation {
                    columns,
                    lookup_set_index: _,
                }) => {
                    // cached = Σ_col α^col · (col_constant + Σ coeff·read), α-compressed by
                    // gkr_lookrel_compress_half (same nesting as VectorizedLookupSetup, but each
                    // slot is a compressed linear relation instead of a raw read). No γ here.
                    assert_eq!(columns.len(), LOOKUP_TABLES_WIDTH, "layout: generic lookup tuple has {} columns, expected {LOOKUP_TABLES_WIDTH}", columns.len());
                    let cols: Vec<Dual> = columns
                        .iter()
                        .map(|column| {
                            let NoFieldLinearRelation {
                                linear_terms,
                                constant,
                            } = column;
                            let linear = linear_terms
                                .iter()
                                .map(|(c, addr)| {
                                    let input = gkraddress_to_calldata(
                                        addr,
                                        i,
                                        layer0_group_widths,
                                        &mut running_max_group_offsets,
                                    );
                                    let c = proth120_const_to_evm(c);
                                    scaled(&c, &input)
                                })
                                .reduce(|acc, el| {
                                    Dual(
                                        format!("{acc} + {el}"),
                                        yul_format!("add({acc:x}, {el:x})"),
                                    )
                                })
                                .unwrap_or_else(|| Dual("0".to_string(), yul_format!("0")));
                            let constant = proth120_const_to_evm(constant);
                            Dual(
                                format!("({constant} + {linear})"),
                                yul_format!("add({constant:x}, {linear:x})"),
                            )
                        })
                        .collect();
                    let compressed = Dual(
                        lookrel_display(&cols),
                        yul_format!("{}", lookrel_horner(&cols)),
                    );
                    yul_println!(
                        "
                    \t{{  // {relation_name}: {compressed} = {output}
                    \t    let gate := {compressed:x}
                    \t    {output:x}
                    \t}}"
                    );
                }
                NoFieldGKRCacheRelation::SingleColumnLookup {
                    relation,
                    range_check_width: _,
                } => {
                    // cached = constant + Σ coeff·read (plain linear relation over deps).
                    let NoFieldLinearRelation {
                        linear_terms,
                        constant,
                    } = &relation.input;
                    let linear = linear_terms
                        .iter()
                        .map(|(c, addr)| {
                            let read = gkraddress_to_calldata(
                                addr,
                                i,
                                layer0_group_widths,
                                &mut running_max_group_offsets,
                            );
                            let c = proth120_const_to_evm(c);
                            scaled(&c, &read)
                        })
                        .reduce(|acc, el| {
                            Dual(format!("{acc} + {el}"), yul_format!("add({acc:x}, {el:x})"))
                        })
                        .unwrap_or_else(|| Dual("0".to_string(), yul_format!("0")));
                    let constant = proth120_const_to_evm(constant);
                    let val = Dual(
                        format!("{constant} + {linear}"),
                        yul_format!("add({constant:x}, {linear:x})"),
                    );
                    yul_println!(
                        "
                    \t{{  // {relation_name}: {val} = {output}
                    \t    let gate := {val:x}
                    \t    {output:x}
                    \t}}"
                    );
                }
                NoFieldGKRCacheRelation::MemoryTuple(rel) => {
                    // cached memory-tuple = gkr_memrel_compress(address_space, addr, ts, val)
                    // from the memory-column at-point evals (calldata). Compute + mstore to slot.
                    let memval = memrel_to_calldata(rel, &mut running_max_group_offsets);
                    yul_println!(
                        "
                    \t{{  // {relation_name}: {memval} = {output}
                    \t    let gate := {memval:x}
                    \t    {output:x}
                    \t}}"
                    );
                }
                _ => todo!("could not match (cached) {cached_relation:?} at layer {i}"),
            }
        }
        // INJECT VIRTUAL POLY CACHES
        let injected_virtualpoly_relations = [
            VirtualSetupPoly::RangeCheck16Bits,
            VirtualSetupPoly::RangeCheckTimestamp,
            VirtualSetupPoly::InitsAndTeardownsLow, // (unified)
            VirtualSetupPoly::InitsAndTeardownsHigh, // (unified)
        ];
        if i == 0 {
            for virtualpoly_relation in injected_virtualpoly_relations {
                let cache_idx = running_cachedoutput_counter + virtualpoly_relation as usize;
                let output = Dual(format!("Cache({cache_idx})"), Yul::mstore(&cache_idx));
                let relation_name = format!("{virtualpoly_relation:?}");
                match virtualpoly_relation {
                    VirtualSetupPoly::RangeCheck16Bits => {
                        assert!(16 <= circuit_rounds);
                        // println!("{relation_name}: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8])(1 - r[7])(1 - r[6])(1 - r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = {output}");
                        yul_println!("
                        \t{{  // {relation_name}: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8])(1 - r[7])(1 - r[6])(1 - r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = {output}
                        \t    let gate := gkr_virtual_poly_rangecheck(16)
                        \t    {output:x}
                        \t}}");
                    }
                    VirtualSetupPoly::RangeCheckTimestamp => {
                        let timestamp_range_bits = cs::definitions::TIMESTAMP_COLUMNS_NUM_BITS;
                        assert!(timestamp_range_bits <= circuit_rounds);
                        // println!("{relation_name}: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8] + 2^16 r[7] + 2^17 r[6] + 2^18 r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = {output}");
                        yul_println!("
                        \t{{  // {relation_name}: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8] + 2^16 r[7] + 2^17 r[6] + 2^18 r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = {output}
                        \t    let gate := gkr_virtual_poly_rangecheck({timestamp_range_bits})
                        \t    {output:x}
                        \t}}");
                    }
                    VirtualSetupPoly::InitsAndTeardownsLow => {
                        assert_eq!(
                            circuit.memory_layout.inits_and_teardowns_word_bits.unwrap(),
                            2,
                            "we expect there to be just 2 empty inits/teardowns low bits"
                        );
                        let low_bits = 16 - 2;
                        assert!(low_bits <= circuit_rounds);
                        // println!("{relation_name}: 4(2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10]) = {output}");
                        yul_println!("
                        \t{{  // {relation_name}: 4(2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10]) = {output}
                        \t    let gate := mul(4, gkr_virtual_poly_compose_vars({low_bits}, 0)) // u32 word-aligned
                        \t    {output:x}
                        \t}}");
                    }
                    VirtualSetupPoly::InitsAndTeardownsHigh => {
                        assert_eq!(
                            circuit.memory_layout.inits_and_teardowns_word_bits.unwrap(),
                            2,
                            "we expect there to be just 2 empty inits/teardowns low bits"
                        );
                        let low_bits = 16 - 2;
                        assert!(low_bits <= circuit_rounds);
                        let high_bits = circuit_rounds - low_bits;
                        assert_eq!(
                            high_bits,
                            prover::gkr::high_bits_offset_for_inits_and_teardowns::<2>(
                                circuit.trace_len
                            )
                        );
                        // println!("{relation_name}: 2^0 r[9] + 2^1 r[8] + 2^2 r[7] + 2^3 r[6] + 2^4 r[5] + 2^5 r[4] + 2^6 r[3] + 2^7 r[2] + 2^8 r[1] + 2^9 r[0] = {output}");
                        yul_println!("
                        \t{{  // {relation_name}: 2^0 r[9] + 2^1 r[8] + 2^2 r[7] + 2^3 r[6] + 2^4 r[5] + 2^5 r[4] + 2^6 r[3] + 2^7 r[2] + 2^8 r[1] + 2^9 r[0] = {output}
                        \t    let gate := gkr_virtual_poly_compose_vars({high_bits}, {low_bits})
                        \t    {output:x}
                        \t}}");
                    }
                }
            }
        }
        // Close the buffered cache function, capture it for top-level hoisting, and emit the
        // inline call (caches are computed + mstore'd before the gates that mload them).
        yul_println!("            }}");
        let layer_cache_func = YUL_BUFFER
            .get()
            .unwrap()
            .lock()
            .unwrap()
            .take()
            .unwrap_or_default();
        // Take (and deactivate) the cache-dep offset collector before the gate loop runs, so it
        // only holds the "extra" (cache-dependency) InnerLayer offsets. Dedup + sort.
        let cache_dep_offsets: Vec<usize> = {
            let mut v = CACHE_DEP_OFFSETS
                .get()
                .unwrap()
                .lock()
                .unwrap()
                .take()
                .unwrap_or_default();
            v.sort_unstable();
            v.dedup();
            v
        };
        let cached_count = cached_relations.len(); // # Cached outputs (in final_step, sorted 0..cached_count)
                                                   // Publish the post-sumcheck calldata cursor to the fixed heap slot so the cache and
                                                   // gate sub-functions can read it via mload(CIRCUIT_PTR) instead of a `ptr` parameter.
        yul_println!("            mstore(CIRCUIT_PTR, ptr)");
        yul_println!("            scl{i}_caches()");
        const DEBUG_NATURAL_GATE_ORDER: bool = false;
        trait EachRefMaybeRev<T, const N: usize> {
            fn each_ref_mayberevmap<U>(&self, f: impl FnMut(&T) -> U) -> [U; N];
        }
        impl<T, const N: usize> EachRefMaybeRev<T, N> for [T; N] {
            fn each_ref_mayberevmap<U>(&self, f: impl FnMut(&T) -> U) -> [U; N] {
                if DEBUG_NATURAL_GATE_ORDER {
                    self.each_ref().map(f)
                } else {
                    self.each_ref_revmap(f)
                }
            }
        }
        let mut running_output_counter = if DEBUG_NATURAL_GATE_ORDER {
            0
        } else {
            previous_input_count
        };
        // Split the gate accumulation into nested sub-functions (own stack frames, hoisted;
        // caches read from heap) so the layer function's stack stays under the EVM limit and
        // dodges the via_ir StackLayoutGenerator bug on the large layer-0 gate code.
        let chunk_size = 12usize;
        let mut chunk_calls: Vec<String> = vec![];
        // compute_claim slots, collected in gate/slot order (same order the g-accumulator
        // processes them): Some(offset) = a real output claim, None = a constraint gate (no
        // output, but still consumes a batching slot). Emitted as sccl{i} after the loop.
        let mut claim_slots: Vec<Option<usize>> = vec![];
        // Layer-0 table-driven max-quadratic gates (size opt): collect every quad/linear term as
        // a packed record (gate `slot`, column indices, coeff) instead of emitting it inline. The
        // gate body becomes a single `mload(GATEVAL+32·slot)`; the terms are summed by compact
        // bucket loops (emitted just before the Horner chunk calls). Only used for i == 0.
        let mut quad_terms: Vec<QTerm> = vec![];
        // Per-gate additive constant terms of the quadratic relations `(gate slot, value)`; only
        // the nonzero ones are kept (they seed GATEVAL[slot] before the term bucket loops add).
        let mut quad_gate_constant_terms: Vec<(u32, u128)> = vec![];
        let mut quad_slot_counter: u32 = 0;
        // Layer-0 size opt: a contiguous run of quadratic gates (consecutive GATEVAL slots) in the
        // current chunk is emitted as ONE Horner loop instead of per-gate steps. `pending_run` holds
        // the open run's slot range `Some((lo, hi_exclusive))`; it is flushed (loop emitted into the
        // current chunk) at a special gate, a chunk boundary, or the end. Stays None for i > 0.
        let mut pending_run: Option<(u32, u32)> = None;
        // Buffer the gate sub-functions so they can be emitted at TOP LEVEL after the layer
        // (nested fns can't reuse ptr/alpha param names — Yul forbids shadowing).
        *YUL_BUFFER
            .get_or_init(|| std::sync::Mutex::new(None))
            .lock()
            .unwrap() = Some(String::new());
        // Reactivate the offset collector for the gate loop to capture the gate INPUT offsets
        // (the sumcheck polys = final_step). extras = cache-deps that are NOT gate inputs.
        *CACHE_DEP_OFFSETS
            .get_or_init(|| std::sync::Mutex::new(None))
            .lock()
            .unwrap() = Some(vec![]);
        for gate_idx in 0..gates.len() {
            if gate_idx % chunk_size == 0 {
                if gate_idx > 0 {
                    // flush any open quad run into the chunk before closing it (runs don't cross chunks)
                    if let Some((lo, hi)) = pending_run.take() {
                        yul_println!("{}", quad_run_loop(lo, hi));
                    }
                    yul_println!("            }}");
                }
                let cidx = gate_idx / chunk_size;
                yul_println!("            function scl{i}_g{cidx}(alpha, a) -> acc {{ acc := a");
                chunk_calls.push(format!("acc := scl{i}_g{cidx}(alpha, acc)"));
            }
            let gate_idx_rev = gates.len() - 1 - gate_idx;
            let gate = &gates[if DEBUG_NATURAL_GATE_ORDER {
                gate_idx
            } else {
                gate_idx_rev
            }];
            let GateArtifacts {
                output_layer,
                enforced_relation,
            } = gate;
            // A run of quadratic gates ends at the first non-quadratic (special) gate: flush it.
            let is_quad_gate = matches!(
                enforced_relation,
                NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { .. }
                    | NoFieldGKRRelation::MaxQuadratic { .. }
            );
            if i == 0 && !is_quad_gate {
                if let Some((lo, hi)) = pending_run.take() {
                    yul_println!("{}", quad_run_loop(lo, hi));
                }
            }
            assert!(*output_layer == i + 1);
            // variant name for comments only (serde_json overflows on Proth120 u128 coeffs).
            let relation_name = {
                let d = format!("{enforced_relation:?}");
                d.split([' ', '{', '(']).next().unwrap_or(&d).to_string()
            };
            let pointcheck_update = yul_format!("acc := add(mulmod(acc, alpha, P), gate)");

            fn gkraddress_to_calldata(
                address: &GKRAddress,
                expected_layer: usize,
                layer0_group_widths: (usize, usize, usize, usize),
                running_max_group_offsets: &mut (usize, usize, usize, usize),
            ) -> Dual {
                let (l0_memvars, l0_witvars, _l0_setupvars, l0_cachevars) = layer0_group_widths;
                let (
                    running_max_memvar,
                    running_max_witvar,
                    running_max_setupvar,
                    running_max_cachevar,
                ) = running_max_group_offsets;
                match address {
                    InnerLayer { layer, offset }
                        if *layer == expected_layer && expected_layer > 0 =>
                    {
                        if let Some(v) = CACHE_DEP_OFFSETS
                            .get_or_init(|| std::sync::Mutex::new(None))
                            .lock()
                            .unwrap()
                            .as_mut()
                        {
                            v.push(*offset);
                        }
                        Dual(format!("[{offset}]"), Yul::calldataload(offset))
                    }
                    GKRAddress::BaseLayerMemory(offset) if expected_layer == 0 => {
                        *running_max_memvar = *offset.max(running_max_memvar);
                        let calldata_offset = *offset; // memory is first in calldata
                        if let Some(v) = CACHE_DEP_OFFSETS
                            .get_or_init(|| std::sync::Mutex::new(None))
                            .lock()
                            .unwrap()
                            .as_mut()
                        {
                            v.push(calldata_offset);
                        }
                        Dual(
                            format!("[{calldata_offset}]"),
                            Yul::calldataload(&calldata_offset),
                        )
                    }
                    GKRAddress::BaseLayerWitness(offset) if expected_layer == 0 => {
                        *running_max_witvar = *offset.max(running_max_witvar);
                        let calldata_offset = l0_memvars + offset; // witness is second in calldata
                        if let Some(v) = CACHE_DEP_OFFSETS
                            .get_or_init(|| std::sync::Mutex::new(None))
                            .lock()
                            .unwrap()
                            .as_mut()
                        {
                            v.push(calldata_offset);
                        }
                        Dual(
                            format!("[{calldata_offset}]"),
                            Yul::calldataload(&calldata_offset),
                        )
                    }
                    GKRAddress::Setup(offset) if expected_layer == 0 => {
                        *running_max_setupvar = *offset.max(running_max_setupvar);
                        let calldata_offset = l0_memvars + l0_witvars + offset; // setup is third in calldata
                        if let Some(v) = CACHE_DEP_OFFSETS
                            .get_or_init(|| std::sync::Mutex::new(None))
                            .lock()
                            .unwrap()
                            .as_mut()
                        {
                            v.push(calldata_offset);
                        }
                        Dual(
                            format!("[{calldata_offset}]"),
                            Yul::calldataload(&calldata_offset),
                        )
                    }
                    GKRAddress::Cached { layer, offset } if *layer == expected_layer => {
                        *running_max_cachevar = *offset.max(running_max_cachevar);
                        Dual(format!("Cache({offset})"), Yul::mload(offset))
                    }
                    GKRAddress::VirtualSetup(virtual_poly) if expected_layer == 0 => {
                        let cache_idx = l0_cachevars + *virtual_poly as usize;
                        *running_max_cachevar = cache_idx.max(*running_max_cachevar);
                        Dual(format!("Cache({cache_idx})"), Yul::mload(&cache_idx))
                    }
                    // GKRAddress::VirtualSetup(virtual_poly) => format!("VirtualSetup{setup:?}(x)")
                    _ => todo!("unexpected address {address:?} for layer {expected_layer}"),
                }
            }
            // Layer-0 table-driven quad gate: assign the gate a GATEVAL slot, collect each of its
            // constant / linear / quadratic terms as a packed record (extracting the operand
            // column index from the calldata expression), and — importantly — call
            // gkraddress_to_calldata for every operand so the gate-input offsets are still recorded
            // for the transcript "extras" the same way the inline path would. Returns the slot.
            fn collect_quad_terms(
                input: &NoFieldMaxQuadraticGKRRelation<Proth120>,
                expected_layer: usize,
                layer0_group_widths: (usize, usize, usize, usize),
                running_max_group_offsets: &mut (usize, usize, usize, usize),
                quad_terms: &mut Vec<QTerm>,
                quad_gate_constant_terms: &mut Vec<(u32, u128)>,
                slot_counter: &mut u32,
            ) -> u32 {
                let slot = *slot_counter;
                *slot_counter += 1;
                let NoFieldMaxQuadraticGKRRelation {
                    quadratic_terms,
                    linear_terms,
                    constant,
                } = input;
                let constant_value = constant.to_u128();
                if constant_value != 0 {
                    quad_gate_constant_terms.push((slot, constant_value));
                }
                for (c, addr) in linear_terms.iter() {
                    let d = gkraddress_to_calldata(
                        addr,
                        expected_layer,
                        layer0_group_widths,
                        running_max_group_offsets,
                    );
                    quad_terms.push(QTerm {
                        slot,
                        a: d.1.calldataload_idx() as u32,
                        b: None,
                        coeff: c.to_u128(),
                    });
                }
                for (addr_a, inner) in quadratic_terms.iter() {
                    let da = gkraddress_to_calldata(
                        addr_a,
                        expected_layer,
                        layer0_group_widths,
                        running_max_group_offsets,
                    );
                    let a = da.1.calldataload_idx() as u32;
                    for (c, addr_b) in inner.iter() {
                        let db = gkraddress_to_calldata(
                            addr_b,
                            expected_layer,
                            layer0_group_widths,
                            running_max_group_offsets,
                        );
                        quad_terms.push(QTerm {
                            slot,
                            a,
                            b: Some(db.1.calldataload_idx() as u32),
                            coeff: c.to_u128(),
                        });
                    }
                }
                slot
            }
            // Returns the output's offset (index into the previous layer's claims array). The
            // caller pushes it into `claim_slots` so compute_claim (sccl{i}) can batch the
            // previous claims in the SAME gate/slot order as the g-accumulator.
            fn gkraddress_to_outputvar(
                address: &GKRAddress,
                expected_layer: usize,
                running_output_counter: &mut usize,
            ) -> usize {
                match address {
                    InnerLayer { layer, offset } if DEBUG_NATURAL_GATE_ORDER && *layer == expected_layer && *offset == *running_output_counter => {
                        *running_output_counter += 1;
                        *offset
                    },
                    InnerLayer { layer, offset } if !DEBUG_NATURAL_GATE_ORDER && *layer == expected_layer && *offset + 1 == *running_output_counter => {
                        *running_output_counter -= 1;
                        *offset
                    },
                    _ => unreachable!("unexpected output address {address:?} for layer {expected_layer} with {running_output_counter} outputs left")
                }
            }
            fn memrelinitparts_to_calldata_inner(
                timestamp_and_value: &InitsOrTeardownsTimestampAndValue,
                running_max_group_offsets: &mut (usize, usize, usize, usize),
            ) -> [Dual; 2] {
                let (
                    running_max_memvar,
                    _running_max_witvar,
                    _running_max_setupvar,
                    _running_max_cachevar,
                ) = running_max_group_offsets;
                match timestamp_and_value {
                    InitsOrTeardownsTimestampAndValue::Init => {
                        let zero1 = Dual(format!("0"), yul_format!("0"));
                        let zero2 = Dual(format!("0"), yul_format!("0"));
                        [zero1, zero2]
                    }
                    InitsOrTeardownsTimestampAndValue::Teardown {
                        lhs_timestamp: [lhs_ts0, lhs_ts1],
                        lhs_value: [lhs_val0, lhs_val1],
                        rhs_timestamp: [rhs_ts0, rhs_ts1],
                        rhs_value: [rhs_val0, rhs_val1],
                    } => {
                        *running_max_memvar = *lhs_ts0.max(running_max_memvar);
                        *running_max_memvar = *lhs_ts1.max(running_max_memvar);
                        *running_max_memvar = *lhs_val0.max(running_max_memvar);
                        *running_max_memvar = *lhs_val1.max(running_max_memvar);
                        *running_max_memvar = *rhs_ts0.max(running_max_memvar);
                        *running_max_memvar = *rhs_ts1.max(running_max_memvar);
                        *running_max_memvar = *rhs_val0.max(running_max_memvar);
                        *running_max_memvar = *rhs_val1.max(running_max_memvar);
                        let lhs_ts0 = Dual(format!("[{lhs_ts0}]"), Yul::calldataload(lhs_ts0));
                        let lhs_ts1 = Dual(format!("[{lhs_ts1}]"), Yul::calldataload(lhs_ts1));
                        let lhs_val0 = Dual(format!("[{lhs_val0}]"), Yul::calldataload(lhs_val0));
                        let lhs_val1 = Dual(format!("[{lhs_val1}]"), Yul::calldataload(lhs_val1));
                        let rhs_ts0 = Dual(format!("[{rhs_ts0}]"), Yul::calldataload(rhs_ts0));
                        let rhs_ts1 = Dual(format!("[{rhs_ts1}]"), Yul::calldataload(rhs_ts1));
                        let rhs_val0 = Dual(format!("[{rhs_val0}]"), Yul::calldataload(rhs_val0));
                        let rhs_val1 = Dual(format!("[{rhs_val1}]"), Yul::calldataload(rhs_val1));
                        [
                            Dual(
                                format!("α³{lhs_ts0} + α⁴{lhs_ts1} + α⁵{lhs_val0} + α⁶{lhs_val1}"),
                                yul_format!("gkr_memrel_compress_high({lhs_ts0:x}, {lhs_ts1:x}, {lhs_val0:x}, {lhs_val1:x})")
                            ),
                            Dual(
                                format!("α³{rhs_ts0} + α⁴{rhs_ts1} + α⁵{rhs_val0} + α⁶{rhs_val1}"),
                                yul_format!("gkr_memrel_compress_high({rhs_ts0:x}, {rhs_ts1:x}, {rhs_val0:x}, {rhs_val1:x})")
                            )
                        ]
                    }
                }
            }
            fn lookrelsingle_to_calldata(
                tuple: &NoFieldSingleColumnLookupRelation<Proth120>,
                expected_layer: usize,
                layer0_group_widths: (usize, usize, usize, usize),
                running_max_group_offsets: &mut (usize, usize, usize, usize),
            ) -> Dual {
                let NoFieldSingleColumnLookupRelation {
                    input,
                    lookup_set_index: _,
                } = tuple;
                let compressed = linrel_to_calldata_inner(
                    input,
                    expected_layer,
                    layer0_group_widths,
                    running_max_group_offsets,
                );
                let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                Dual(
                    format!("({logup_gamma} + {compressed})"),
                    yul_format!("add({logup_gamma:x}, {compressed:x})"),
                )
            }
            fn lookrelgeneric_to_calldata(
                tuple: &NoFieldVectorLookupRelation<Proth120>,
                expected_layer: usize,
                layer0_group_widths: (usize, usize, usize, usize),
                running_max_group_offsets: &mut (usize, usize, usize, usize),
            ) -> Dual {
                let NoFieldVectorLookupRelation {
                    columns,
                    lookup_set_index: _,
                } = tuple;
                assert_eq!(
                    columns.len(),
                    LOOKUP_TABLES_WIDTH,
                    "layout: generic lookup tuple has {} columns, expected {LOOKUP_TABLES_WIDTH}",
                    columns.len()
                );
                let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                let logup_alpha = Dual("β".to_string(), Yul::logup_alpha());
                let cols: Vec<Dual> = columns
                    .iter()
                    .enumerate()
                    .map(|(j, column)| {
                        let compressed_column = linrel_to_calldata_inner(
                            column,
                            expected_layer,
                            layer0_group_widths,
                            running_max_group_offsets,
                        );
                        let logup_alpha_j = logup_alpha.0.clone() + &superscript(j);
                        Dual(
                            format!("{logup_alpha_j}({compressed_column})"),
                            yul_format!("{compressed_column:x}"),
                        )
                    })
                    .collect();
                Dual(
                    format!("({logup_gamma} + {})", lookrel_display(&cols)),
                    yul_format!("add({logup_gamma:x}, {})", lookrel_horner(&cols)),
                )
            }
            fn linrel_to_calldata_inner(
                inputs: &NoFieldLinearRelation<Proth120>,
                expected_layer: usize,
                layer0_group_widths: (usize, usize, usize, usize),
                running_max_group_offsets: &mut (usize, usize, usize, usize),
            ) -> Dual {
                let NoFieldLinearRelation {
                    linear_terms,
                    constant,
                } = inputs;
                let linear = linear_terms
                    .iter()
                    .map(|(c, addr)| {
                        let input = gkraddress_to_calldata(
                            addr,
                            expected_layer,
                            layer0_group_widths,
                            running_max_group_offsets,
                        );
                        let c = proth120_const_to_evm(c);
                        scaled(&c, &input)
                    })
                    .reduce(|acc, el| {
                        Dual(format!("{acc} + {el}"), yul_format!("add({acc:x}, {el:x})"))
                    })
                    .unwrap_or(Dual("0".to_string(), yul_format!("0")));
                let constant = proth120_const_to_evm(constant);
                Dual(
                    format!("{constant} + {linear}"),
                    yul_format!("add({constant:x}, {linear:x})"),
                )
            }
            fn quadrel_to_calldata_inner(
                input: &NoFieldMaxQuadraticGKRRelation<Proth120>,
                expected_layer: usize,
                layer0_group_widths: (usize, usize, usize, usize),
                running_max_group_offsets: &mut (usize, usize, usize, usize),
            ) -> Dual {
                // eval_max_quadratic: constant + Σ_a read_a·(Σ_b coeff·read_b) + Σ coeff·read.
                // Products via mulmod (reduced); sums via add (non-canonical, funneled through
                // the outer mulmod in pointcheck_update). Mirrors the validated Rust kernel.
                let NoFieldMaxQuadraticGKRRelation {
                    quadratic_terms,
                    linear_terms,
                    constant,
                } = input;
                let zero = || Dual("0".to_string(), yul_format!("0"));
                let quadratic = quadratic_terms
                    .iter()
                    .map(|(address, inner_terms)| {
                        let read = gkraddress_to_calldata(
                            address,
                            expected_layer,
                            layer0_group_widths,
                            running_max_group_offsets,
                        );
                        let inner = inner_terms
                            .iter()
                            .map(|(c, address)| {
                                let read = gkraddress_to_calldata(
                                    address,
                                    expected_layer,
                                    layer0_group_widths,
                                    running_max_group_offsets,
                                );
                                let c = proth120_const_to_evm(c);
                                scaled(&c, &read)
                            })
                            .reduce(|acc, el| {
                                Dual(format!("{acc} + {el}"), yul_format!("add({acc:x}, {el:x})"))
                            })
                            .unwrap_or_else(zero);
                        Dual(
                            format!("{read}({inner})"),
                            yul_format!("mulmod({read:x}, {inner:x}, P)"),
                        )
                    })
                    .reduce(|acc, el| {
                        Dual(format!("{acc} + {el}"), yul_format!("add({acc:x}, {el:x})"))
                    })
                    .unwrap_or_else(zero);
                let linear = linear_terms
                    .iter()
                    .map(|(c, address)| {
                        let read = gkraddress_to_calldata(
                            address,
                            expected_layer,
                            layer0_group_widths,
                            running_max_group_offsets,
                        );
                        let c = proth120_const_to_evm(c);
                        scaled(&c, &read)
                    })
                    .reduce(|acc, el| {
                        Dual(format!("{acc} + {el}"), yul_format!("add({acc:x}, {el:x})"))
                    })
                    .unwrap_or_else(zero);
                let constant = proth120_const_to_evm(constant);
                Dual(
                    format!("{constant} + {linear} + {quadratic}"),
                    yul_format!("add(add({constant:x}, {linear:x}), {quadratic:x})"),
                )
            }
            // fn expression_to_calldata(expression: &NoFieldStructuredExpression, expected_layer: usize, layer0_group_widths: (usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize)) -> String {
            //    match expression {
            //         NoFieldStructuredExpression::Constant(c) => proth120_const_to_evm(c),
            //         NoFieldStructuredExpression::Place(address) => gkraddress_to_calldata(address, expected_layer, layer0_group_widths, running_max_group_offsets),
            //         NoFieldStructuredExpression::Sum(terms) => {
            //             let term = terms.iter().map(|expression| {
            //                 expression_to_calldata(expression, expected_layer, layer0_group_widths, running_max_group_offsets)
            //             }).collect::<Vec<_>>().join(" + ");
            //             format!("({term})")
            //         }
            //         NoFieldStructuredExpression::Product(terms) => {
            //             // assert!(terms.len() <= 2, "we dont tolerate degree > 2 expressions");
            //             let num_constants = terms.iter().filter(|term| {
            //                 matches!(term, NoFieldStructuredExpression::Constant(_))
            //             }).count();
            //             assert!(num_constants <= 1); // makes rendering faulty if more
            //             let term = terms.iter().map(|expression| {
            //                 expression_to_calldata(expression, expected_layer, layer0_group_widths, running_max_group_offsets)
            //             }).collect::<Vec<_>>().join("");
            //             term
            //         }
            //    }
            // }

            match enforced_relation {
                // 3
                NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                    let [[num1, den1], [num2, den2]] = input.each_ref().map(|pair| {
                        pair.each_ref().map(|addr| {
                            gkraddress_to_calldata(
                                addr,
                                i,
                                layer0_group_widths,
                                &mut running_max_group_offsets,
                            )
                        })
                    });
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| {
                        gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter)
                    });
                    claim_slots.push(Some(den_out));
                    claim_slots.push(Some(num_out));
                    // println!("{relation_name}: {num1}/{den1} + {num2}/{den2} = {num_out}/{den_out}");
                    yul_println!("
                    \t// {relation_name}: {num1}/{den1} + {num2}/{den2} = {num_out}/{den_out}
                    \tacc := gate_aggregatelookuprationalpair(alpha, acc, {num1:o}, {num2:o}, {den1:o}, {den2:o})
                    \t");
                }
                NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                    let input = gkraddress_to_calldata(
                        input,
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let output =
                        gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    claim_slots.push(Some(output));
                    // println!("{relation_name}: {input} = {output}");
                    yul_println!(
                        "
                    \t// {relation_name}: {input} = {output}
                    \tacc := gate_copyinextensionfield(alpha, acc, {input:o})
                    \t"
                    );
                }

                // 2
                NoFieldGKRRelation::MaskIntoIdentityProduct {
                    input,
                    mask,
                    output,
                } => {
                    let input = gkraddress_to_calldata(
                        input,
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let mask = gkraddress_to_calldata(
                        mask,
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let output =
                        gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    claim_slots.push(Some(output));
                    // println!("{relation_name}: {input}*{mask} + (1-{mask}) = {output}");
                    yul_println!(
                        "
                    \t// {relation_name}: {input}*{mask} + (1-{mask}) = {output}
                    \tacc := gate_maskintoidentityproduct(alpha, acc, {input:o}, {mask:o})
                    \t"
                    );
                }

                // 1
                NoFieldGKRRelation::CopyInBaseField { input, output } => {
                    let input = gkraddress_to_calldata(
                        input,
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let output =
                        gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    claim_slots.push(Some(output));
                    // println!("{relation_name}: {input} = {output}");
                    yul_println!(
                        "
                    \t{{  // {relation_name}: {input} = {output}
                    \t    let gate := {input:x}
                    \t    {pointcheck_update:x}
                    \t}}"
                    );
                }
                NoFieldGKRRelation::TrivialProduct { input, output }
                | NoFieldGKRRelation::InitialGrandProductFromCaches { input, output } => {
                    let [lhs, rhs] = input.each_ref().map(|addr| {
                        gkraddress_to_calldata(
                            addr,
                            i,
                            layer0_group_widths,
                            &mut running_max_group_offsets,
                        )
                    });
                    let output =
                        gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    claim_slots.push(Some(output));
                    // println!("{relation_name}: {lhs}*{rhs} = {output}");
                    yul_println!(
                        "
                    \t{{  // {relation_name}: {lhs}*{rhs} = {output}
                    \t    let gate := mulmod({lhs:x}, {rhs:x}, P)
                    \t    {pointcheck_update:x}
                    \t}}"
                    );
                }
                NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                    input,
                    remainder,
                    output,
                }
                | NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                    input,
                    remainder,
                    output,
                } => {
                    let [num, den] = input.each_ref().map(|addr| {
                        gkraddress_to_calldata(
                            addr,
                            i,
                            layer0_group_widths,
                            &mut running_max_group_offsets,
                        )
                    });
                    let remainder = gkraddress_to_calldata(
                        remainder,
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| {
                        gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter)
                    });
                    claim_slots.push(Some(den_out));
                    claim_slots.push(Some(num_out));
                    let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                    // println!("{relation_name}: {num}/{den} + 1/({logup_gamma} + {remainder}) = {num_out}/{den_out}");
                    yul_println!("
                    \t{{  // {relation_name}: {num}/{den} + 1/({logup_gamma} + {remainder}) = {num_out}/{den_out}
                    \t    let den_out := mulmod({den:x}, add({logup_gamma:x}, {remainder:x}), P)
                    \t    let gate := den_out
                    \t    {pointcheck_update:x}
                    \t    let num_out := add(mulmod({num:x}, add({logup_gamma:x}, {remainder:x}), P), {den:x})
                    \t    gate := num_out
                    \t    {pointcheck_update:x}
                    \t}}");
                }
                // (unified)
                NoFieldGKRRelation::LookupPairFromVectorInputs { input, output } => {
                    let [den1, den2] = input.each_ref().map(|input| {
                        lookrelgeneric_to_calldata(
                            input,
                            i,
                            layer0_group_widths,
                            &mut running_max_group_offsets,
                        )
                    });
                    let [num_out, den_out] = output.each_ref_mayberevmap(|address| {
                        gkraddress_to_outputvar(address, i + 1, &mut running_output_counter)
                    });
                    claim_slots.push(Some(den_out));
                    claim_slots.push(Some(num_out));
                    // println!("{relation_name}: 1/{den1} + 1/{den2} = {num_out}/{den_out}");
                    yul_println!(
                        "
                    \t{{  // {relation_name}: 1/{den1} + 1/{den2} = {num_out}/{den_out}
                    \t    let den1 := {den1:x} // for generic lookups we collect
                    \t    let den2 := {den2:x} // for generic lookups we collect
                    \t    let den_out := mulmod(den1, den2, P)
                    \t    let gate := den_out
                    \t    {pointcheck_update:x}
                    \t    let num_out := add(den1, den2)
                    \t    gate := num_out
                    \t    {pointcheck_update:x}
                    \t}}"
                    );
                }
                NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
                    input,
                    remainder,
                    output,
                } => {
                    let [num1, den1] = input.each_ref().map(|address| {
                        gkraddress_to_calldata(
                            address,
                            i,
                            layer0_group_widths,
                            &mut running_max_group_offsets,
                        )
                    });
                    let den2 = lookrelgeneric_to_calldata(
                        remainder,
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let [num_out, den_out] = output.each_ref_mayberevmap(|address| {
                        gkraddress_to_outputvar(address, i + 1, &mut running_output_counter)
                    });
                    claim_slots.push(Some(den_out));
                    claim_slots.push(Some(num_out));
                    // println!("{relation_name}: {num1}/{den1} + 1/{den2} = {num_out}/{den_out}")
                    yul_println!(
                        "
                    \t{{  // {relation_name}: {num1}/{den1} + 1/{den2} = {num_out}/{den_out}
                    \t    let den2 := {den2:x} // for generic lookups we collect
                    \t    let den_out := mulmod({den1:x}, den2, P)
                    \t    let gate := den_out
                    \t    {pointcheck_update:x}
                    \t    let num_out := add(mulmod({num1:x}, den2, P), {den1:x})
                    \t    gate := num_out
                    \t    {pointcheck_update:x}
                    \t}}"
                    );
                }

                // 0
                NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
                    let [lhs, rhs] = input.each_ref().map(|contribution| {
                        memrel_to_calldata(contribution, &mut running_max_group_offsets)
                    });
                    let output =
                        gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    claim_slots.push(Some(output));
                    // println!("{relation_name}: {lhs}*{rhs} = {output}");
                    yul_println!(
                        "
                    \t{{  // {relation_name}: {lhs}*{rhs} = {output}
                    \t    let lhs := {lhs:x} // for memrel we collect
                    \t    let rhs := {rhs:x} // for memrel we collect
                    \t    let gate := mulmod(lhs, rhs, P)
                    \t    {pointcheck_update:x}
                    \t}}"
                    );
                }
                NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                    input,
                    setup,
                    output,
                } => {
                    let input = gkraddress_to_calldata(
                        input,
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let [multiplicity, setup] = setup.each_ref().map(|address| {
                        gkraddress_to_calldata(
                            address,
                            i,
                            layer0_group_widths,
                            &mut running_max_group_offsets,
                        )
                    });
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| {
                        gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter)
                    });
                    claim_slots.push(Some(den_out));
                    claim_slots.push(Some(num_out));
                    let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                    // println!("{relation_name}: 1/({logup_gamma} + {input}) - {multiplicity}/({logup_gamma} + {setup}) = {num_out}/{den_out}");
                    yul_println!("
                    \t{{  // {relation_name}: 1/({logup_gamma} + {input}) - {multiplicity}/({logup_gamma} + {setup}) = {num_out}/{den_out}
                    \t    let den_out := mulmod(add({logup_gamma:x}, {input:x}), add({logup_gamma:x}, {setup:x}), P)
                    \t    let gate := den_out
                    \t    {pointcheck_update:x}
                    \t    let num_out := add(add({logup_gamma:x}, {setup:x}), sub(P, mulmod({multiplicity:x}, add({logup_gamma:x}, {input:x}), P)))
                    \t    gate := num_out
                    \t    {pointcheck_update:x}
                    \t}}");
                }
                NoFieldGKRRelation::LookupPairFromBaseInputs {
                    input,
                    output,
                    range_check_width: _,
                } => {
                    let [den1, den2] = input.each_ref().map(|relation| {
                        lookrelsingle_to_calldata(
                            relation,
                            i,
                            layer0_group_widths,
                            &mut running_max_group_offsets,
                        )
                    });
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| {
                        gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter)
                    });
                    claim_slots.push(Some(den_out));
                    claim_slots.push(Some(num_out));
                    // println!("{relation_name}: 1/{den1} + 1/{den2} = {num_out}/{den_out}");
                    // TODO: THIS ADDS A LOT OF BYTECODE (+10%)
                    yul_println!(
                        "
                    \t{{  // {relation_name}: 1/{den1} + 1/{den2} = {num_out}/{den_out}
                    \t    let den_out := mulmod({den1:x}, {den2:x}, P)
                    \t    let gate := den_out
                    \t    {pointcheck_update:x}
                    \t    let num_out := add({den1:x}, {den2:x})
                    \t    gate := num_out
                    \t    {pointcheck_update:x}
                    \t}}"
                    );
                }
                NoFieldGKRRelation::MaterializeSingleLookupInput {
                    input,
                    output,
                    range_check_width: _,
                } => {
                    let NoFieldSingleColumnLookupRelation {
                        input,
                        lookup_set_index: _,
                    } = input;
                    let compressed_tuple = linrel_to_calldata_inner(
                        input,
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let output =
                        gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    claim_slots.push(Some(output));
                    // println!("{relation_name}: {compressed_tuple} = {output}");
                    yul_println!(
                        "
                    \t{{  // {relation_name}: {compressed_tuple} = {output}
                    \t    let gate := {compressed_tuple:x}
                    \t    {pointcheck_update:x}
                    \t}}"
                    );
                }
                // NoFieldGKRRelation::LookupWithDensAndCachedSetup { input, setup, output } => {
                NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
                    input,
                    setup,
                    output,
                } => {
                    let (input_mask, input_den) = input;
                    let (setup_multiplicity, setup_terms) = setup;
                    let input_mask = gkraddress_to_calldata(
                        input_mask,
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let input_den = lookrelgeneric_to_calldata(
                        input_den,
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let setup_multiplicity = gkraddress_to_calldata(
                        setup_multiplicity,
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let logup_alpha = Dual("β".to_string(), Yul::logup_alpha());
                    assert_eq!(setup_terms.len(), LOOKUP_TABLES_WIDTH, "layout: generic lookup setup tuple has {} columns, expected {LOOKUP_TABLES_WIDTH}", setup_terms.len());
                    let setup = {
                        let sets: Vec<Dual> = setup_terms
                            .iter()
                            .enumerate()
                            .map(|(j, addr)| {
                                let input = gkraddress_to_calldata(
                                    addr,
                                    i,
                                    layer0_group_widths,
                                    &mut running_max_group_offsets,
                                );
                                let beta_j = logup_alpha.0.clone() + &superscript(j);
                                Dual(format!("{beta_j}{input}"), yul_format!("{input:x}"))
                            })
                            .collect();
                        Dual(
                            lookrel_display(&sets),
                            yul_format!("{}", lookrel_horner(&sets)),
                        )
                    };
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| {
                        gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter)
                    });
                    claim_slots.push(Some(den_out));
                    claim_slots.push(Some(num_out));
                    let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                    // println!("{relation_name}: {input_mask}/{input_den} - {setup_multiplicity}/({logup_gamma} + {setup}) = {num_out}/{den_out}");
                    yul_println!("
                    \t{{  // {relation_name}: {input_mask}/{input_den} - {setup_multiplicity}/({logup_gamma} + {setup}) = {num_out}/{den_out}
                    \t    let input_den := {input_den:x} // for generic lookups we collect
                    \t    let setup_den := add({logup_gamma:x}, {setup:x}) // for generic lookups we collect
                    \t    let den_out := mulmod(input_den, setup_den, P)
                    \t    let gate := den_out
                    \t    {pointcheck_update:x}
                    \t    let num_out := add(mulmod({input_mask:x}, setup_den, P), sub(P, mulmod(input_den, {setup_multiplicity:x}, P)))
                    \t    gate := num_out
                    \t    {pointcheck_update:x}
                    \t}}");
                }
                // NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input, expression } => {
                NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input, .. } => {
                    // Constraint gate: contributes a g slot (val==0 when satisfied) but no output
                    // claim — compute_claim skips it (advances the batching slot only).
                    claim_slots.push(None);
                    if i == 0 {
                        // Table-driven: collect terms (which also records the gate-input offsets
                        // for the transcript, via gkraddress_to_calldata). The Horner step is not
                        // emitted here — the gate extends the current quad run, flushed as a loop.
                        let slot = collect_quad_terms(
                            input,
                            i,
                            layer0_group_widths,
                            &mut running_max_group_offsets,
                            &mut quad_terms,
                            &mut quad_gate_constant_terms,
                            &mut quad_slot_counter,
                        );
                        pending_run = Some(match pending_run {
                            None => (slot, slot + 1),
                            Some((lo, hi)) => {
                                debug_assert_eq!(hi, slot, "quad run slots must be consecutive");
                                (lo, slot + 1)
                            }
                        });
                    } else {
                        let input = quadrel_to_calldata_inner(
                            input,
                            i,
                            layer0_group_widths,
                            &mut running_max_group_offsets,
                        );
                        yul_println!(
                            "
                        \t{{  // {relation_name}: 0 == {input}
                        \t    let gate := {input:x}
                        \t    {pointcheck_update:x}
                        \t}}"
                        );
                    }
                }
                // (unified)
                NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                    timestamp_and_value,
                    setup,
                    output,
                    set_idxes,
                } => {
                    let [setup_low, setup_high] = setup.each_ref().map(|address| {
                        gkraddress_to_calldata(
                            address,
                            i,
                            layer0_group_widths,
                            &mut running_max_group_offsets,
                        )
                    });
                    let [lhs_addr_high, rhs_addr_high] = {
                        assert_eq!(
                            circuit.trace_len,
                            1 << 22,
                            "currently we expect gkr_compress to go up to 2^22"
                        );
                        assert_eq!(
                            circuit.memory_layout.inits_and_teardowns_word_bits.unwrap(),
                            2,
                            "we expect there to be just 2 empty low bits"
                        );
                        let high_bits_shift = prover::gkr::high_bits_offset_for_inits_and_teardowns::<
                            2,
                        >(circuit.trace_len);
                        let memory_alpha2 = Dual(format!("α²"), Yul::memory_alpha(1));
                        // The set-window is `top_bits[set_idx] << high_bits_shift`, NOT `set_idx << shift`.
                        // `top_bits` (the RAM-set base chunk indices) are data-dependent and cannot be
                        // derived from the circuit, so read them from the transcript preimage in calldata:
                        // layout is registers ‖ final_pc/ts then top_bits[..] as LE u32.
                        set_idxes.map(|c| {
                            let byteoff = super::PREIMAGE_TOP_BITS_BYTE_OFFSET + (c as usize) * 4;
                            Dual(
                                format!("{memory_alpha2}({setup_high} + (topbits[{c}]<<{high_bits_shift}))"),
                                yul_format!("mulmod({memory_alpha2:x}, add({setup_high:x}, shl({high_bits_shift}, gkr_inits_teardowns_topbits({byteoff}))), P)")
                            )
                        })
                    };
                    let [lhs_timestamp_and_value, rhs_timestamp_and_value] =
                        memrelinitparts_to_calldata_inner(
                            timestamp_and_value,
                            &mut running_max_group_offsets,
                        );
                    let output =
                        gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    claim_slots.push(Some(output));
                    let shared = {
                        let address_space = AddressSpaceType::RAM as u32;
                        let memory_gamma = Dual(format!("γ"), Yul::memory_gamma());
                        let memory_alpha1 = Dual(format!("α"), Yul::memory_alpha(0));
                        Dual(format!("{memory_gamma} + {address_space} + {memory_alpha1}{setup_low}"), yul_format!("add(add({memory_gamma:x}, {address_space}), mulmod({memory_alpha1:x}, {setup_low:x}, P))"))
                    };
                    // println!("{relation_name}: ({shared} + {lhs_addr_high} + {lhs_timestamp_and_value}) * ({shared} + {rhs_addr_high} + {rhs_timestamp_and_value}) = {output}");
                    yul_println!("
                    \t{{  // {relation_name}: ({shared} + {lhs_addr_high} + {lhs_timestamp_and_value}) * ({shared} + {rhs_addr_high} + {rhs_timestamp_and_value}) = {output}
                    \t    let shared := {shared:x}
                    \t    let lhs := add(shared, add({lhs_addr_high:x}, {lhs_timestamp_and_value:x})) // for memrel we collect
                    \t    let rhs := add(shared, add({rhs_addr_high:x}, {rhs_timestamp_and_value:x})) // for memrel we collect
                    \t    let gate := mulmod(lhs, rhs, P)
                    \t    {pointcheck_update:x}
                    \t}}");
                }
                NoFieldGKRRelation::MaxQuadratic { input, output, .. } => {
                    let output =
                        gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    claim_slots.push(Some(output));
                    if i == 0 {
                        // Extend the current quad run (Horner step deferred to the run loop).
                        let slot = collect_quad_terms(
                            input,
                            i,
                            layer0_group_widths,
                            &mut running_max_group_offsets,
                            &mut quad_terms,
                            &mut quad_gate_constant_terms,
                            &mut quad_slot_counter,
                        );
                        pending_run = Some(match pending_run {
                            None => (slot, slot + 1),
                            Some((lo, hi)) => {
                                debug_assert_eq!(hi, slot, "quad run slots must be consecutive");
                                (lo, slot + 1)
                            }
                        });
                    } else {
                        let input = quadrel_to_calldata_inner(
                            input,
                            i,
                            layer0_group_widths,
                            &mut running_max_group_offsets,
                        );
                        yul_println!(
                            "
                        \t{{  // {relation_name}: {input} = {output}
                        \t    let gate := {input:x}
                        \t    {pointcheck_update:x}
                        \t}}"
                        );
                    }
                }

                NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { input, output }
                | NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                    // LookupInitialPair with direct-address inputs: den1=γ+in0, den2=γ+in1;
                    // den_out = den1·den2, num_out = den1+den2.
                    let [b, d] = input.each_ref().map(|addr| {
                        gkraddress_to_calldata(
                            addr,
                            i,
                            layer0_group_widths,
                            &mut running_max_group_offsets,
                        )
                    });
                    let [num_out, den_out] = output.each_ref_mayberevmap(|address| {
                        gkraddress_to_outputvar(address, i + 1, &mut running_output_counter)
                    });
                    claim_slots.push(Some(den_out));
                    claim_slots.push(Some(num_out));
                    let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                    yul_println!("
                    \t{{  // {relation_name}: 1/({logup_gamma}+{b}) + 1/({logup_gamma}+{d}) = {num_out}/{den_out}
                    \t    let den1 := add({logup_gamma:x}, {b:x})
                    \t    let den2 := add({logup_gamma:x}, {d:x})
                    \t    let den_out := mulmod(den1, den2, P)
                    \t    let gate := den_out
                    \t    {pointcheck_update:x}
                    \t    let num_out := add(den1, den2)
                    \t    gate := num_out
                    \t    {pointcheck_update:x}
                    \t}}");
                }
                NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                    input,
                    setup,
                    output,
                } => {
                    // num = a·(d+δ) − c·(b+δ), den = (b+δ)(d+δ); a=input0,b=input1,c=setup0,d=setup1.
                    let a = gkraddress_to_calldata(
                        &input[0],
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let b = gkraddress_to_calldata(
                        &input[1],
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let c = gkraddress_to_calldata(
                        &setup[0],
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let d = gkraddress_to_calldata(
                        &setup[1],
                        i,
                        layer0_group_widths,
                        &mut running_max_group_offsets,
                    );
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| {
                        gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter)
                    });
                    claim_slots.push(Some(den_out));
                    claim_slots.push(Some(num_out));
                    let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                    yul_println!("
                    \t{{  // {relation_name}: (({a})·(({d})+δ) − ({c})·(({b})+δ)) / ((({b})+δ)(({d})+δ)) = {num_out}/{den_out}
                    \t    let bg := add({logup_gamma:x}, {b:x})
                    \t    let dg := add({logup_gamma:x}, {d:x})
                    \t    let den_out := mulmod(bg, dg, P)
                    \t    let gate := den_out
                    \t    {pointcheck_update:x}
                    \t    let num_out := add(mulmod({a:x}, dg, P), sub(mul(2, P), mulmod({c:x}, bg, P)))
                    \t    gate := num_out
                    \t    {pointcheck_update:x}
                    \t}}");
                }
                _ => todo!("could not match {enforced_relation:?} at layer {i}"),
            }
        }
        // Take the gate-input offsets (final_step / sumcheck polys). The transcript "extras"
        // are the cache dependencies that are NOT gate inputs.
        let gate_input_offsets: std::collections::HashSet<usize> = CACHE_DEP_OFFSETS
            .get()
            .unwrap()
            .lock()
            .unwrap()
            .take()
            .unwrap_or_default()
            .into_iter()
            .collect();
        let cache_dep_offsets: Vec<usize> = {
            let mut v: Vec<usize> = cache_dep_offsets
                .into_iter()
                .filter(|o| !gate_input_offsets.contains(o))
                .collect();
            v.sort_unstable();
            v.dedup();
            v
        };
        // close the last gate sub-function (into the buffer), capture the sub-functions, then
        // call them all in order (Horner acc accumulation) inline in the layer function.
        let layer_chunk_funcs = if !gates.is_empty() {
            // flush a quad run still open in the last chunk before closing it
            if let Some((lo, hi)) = pending_run.take() {
                yul_println!("{}", quad_run_loop(lo, hi));
            }
            yul_println!("            }}"); // close last chunk (still buffered)
            let funcs = YUL_BUFFER
                .get()
                .unwrap()
                .lock()
                .unwrap()
                .take()
                .unwrap_or_default();
            // Layer-0 size opt: fill GATEVAL[] from the packed term table (compact bucket loops,
            // modulus in a stack local) BEFORE the Horner chunk calls read it. Emitted into the
            // layer body (main output; YUL_BUFFER is drained above so yul_println! targets it).
            if i == 0 && !quad_terms.is_empty() {
                yul_println!(
                    "{}",
                    emit_layer0_quad_table(&quad_terms, &quad_gate_constant_terms)
                );
            }
            for call in &chunk_calls {
                yul_println!("            {call}");
            }
            funcs
        } else {
            *YUL_BUFFER.get().unwrap().lock().unwrap() = None;
            String::new()
        };

        assert_eq!(
            running_output_counter,
            if DEBUG_NATURAL_GATE_ORDER {
                previous_input_count
            } else {
                0
            }
        );
        if i > 0 {
            // (with-caches: inner layers CAN have cached relations now — handled above.)
            previous_input_count = intermediate_layer_width.unwrap();
        } else {
            let (l0_memvars, l0_witvars, l0_setupvars, l0_cachevars) = layer0_group_widths;
            let (
                running_max_memvar,
                running_max_witvar,
                running_max_setupvar,
                running_max_cachevar,
            ) = running_max_group_offsets;
            // `running_max_*` stays 0 whether offset 0 was seen or the group is
            // empty, so only enforce `max + 1 == width` for non-empty groups.
            let assert_group_width = |running_max: usize, width: usize| {
                if width == 0 {
                    assert_eq!(running_max, 0);
                } else {
                    assert_eq!(running_max + 1, width);
                }
            };
            assert_group_width(running_max_memvar, l0_memvars);
            assert_group_width(running_max_witvar, l0_witvars);
            assert_group_width(running_max_setupvar, l0_setupvars);
            assert_group_width(
                running_max_cachevar,
                l0_cachevars + injected_virtualpoly_relations.len(),
            );
            previous_input_count = l0_memvars + l0_witvars + l0_setupvars;
        }

        // compute_claim (sccl{i}): batch the previous layer's claims (heap array) in the SAME
        // gate/slot order as the g-accumulator, so the initial claim's per-slot batching powers
        // match `g`, making the point-check identity hold. The first-executed layer (highest i)
        // reads the dim-reduce output (GKR_CLAIMS_PTR); the rest read the threaded array that the
        // previous layer wrote (GKR_CIRCUIT_CLAIMS_PTR). Plain Horner in alpha -> shallow (2 vars).
        let claims_src = if i == circuit.layers.len() - 1 {
            "GKR_CLAIMS_PTR()"
        } else {
            "GKR_CIRCUIT_CLAIMS_PTR()"
        };
        let sccl_func = {
            let mut body = String::new();
            for slot in &claim_slots {
                match slot {
                    Some(off) => body.push_str(&format!("            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, {off}))))\n")),
                    None => body.push_str("            claim := mulmod(claim, alpha, P)\n"),
                }
            }
            format!("            function sccl{i}(alpha) -> claim {{\n            let src := {claims_src}\n            claim := 0\n{body}            }}\n")
        };
        // Writeback: publish this layer's at-point evals (offset-indexed, at CIRCUIT_PTR) to the
        // threaded claims array for the next-executed layer. The last-executed layer (i==0) has
        // no next layer. Count == previous_input_count (this layer's absorbed eval count).
        let writeback = if i > 0 {
            // This writeback loop reads every one of the {previous_input_count} calldata lanes
            // ([0,n) = final_step gate inputs ++ extras) that the claims_batch absorbs below, so a
            // `< P` check here makes the absorbed transcript bytes canonical (bind to the reduced
            // value, not the prover's 16-byte encoding) while reusing the read it already performs.
            format!(
                "
            // WRITEBACK claims for next layer ({previous_input_count} evals) + canonicity guard
            \tfor {{ let wk := 0 }} lt(wk, {previous_input_count}) {{ wk := add(wk, 1) }} {{
            \t    let cv := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk))))
            \t    if iszero(lt(cv, P)) {{ revert(0, 0) }}
            \t    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), cv)
            \t}}"
            )
        } else {
            // Base layer has no writeback, but the same guard is needed over the n0 at-point
            // evals (mem++wit++setup) the base-layer claims_batch absorbs from calldata.
            let n0 = layer0_group_widths.0 + layer0_group_widths.1 + layer0_group_widths.2;
            format!("
            // canonicity guard for the base-layer claims_batch absorb: {n0} at-point evals from
            // calldata; require each < P so the absorbed transcript bytes are canonical
            \tfor {{ let wk := 0 }} lt(wk, {n0}) {{ wk := add(wk, 1) }} {{
            \t    if iszero(lt(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk)))), P)) {{ revert(0, 0) }}
            \t}}")
        };

        // Transcript (absorb evals + draw next batching). For layers WITHOUT caches the whole
        // eval block is one contiguous absorb (sumcheck_claims_batch). For cache layers the
        // absorbed data is final_step = [gate-input InnerLayer evals ++ the recomputed cache evals]
        // (address-sorted: InnerLayer < Cached) FOLLOWED BY the extras = the cache-dependency
        // InnerLayer evals — all absorbed into ONE keccak BEFORE drawing next_batching (soundness:
        // the batching challenge must depend on the extra prover-provided evals too, matching the
        // prover committing `new_claims ++ extra` in one shot). The keccak transcript hashes
        // `seed || data` per absorb, so final_step and extras must go into a single absorb — two
        // separate absorbs would diverge from the prover's single commit.
        fn contiguous_ranges(sorted: &[usize]) -> Vec<(usize, usize)> {
            let mut r = vec![];
            let mut k = 0;
            while k < sorted.len() {
                let start = sorted[k];
                let mut j = k;
                while j + 1 < sorted.len() && sorted[j + 1] == sorted[j] + 1 {
                    j += 1;
                }
                r.push((start, sorted[j] - start + 1));
                k = j + 1;
            }
            r
        }
        let claims_batch = if cached_count > 0 {
            let extra_set: std::collections::HashSet<usize> =
                cache_dep_offsets.iter().copied().collect();
            let cd_ranges = |offs: &[usize]| -> String {
                contiguous_ranges(offs).iter().map(|(s, l)|
                    format!("            calldatacopy(bp, add(base, mul(16, {s})), mul(16, {l}))\n            bp := add(bp, mul(16, {l}))\n")
                ).collect()
            };
            let cache_reads = |slots: &[usize]| -> String {
                slots.iter().map(|c|
                    format!("            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, {c})))))\n            bp := add(bp, 16)\n")
                ).collect()
            };
            // Build final_step (absorbed before the batching draw) and extras (after) in
            // GKRAddress-sort order. Inner layer: InnerLayer inputs then Cached. Base layer:
            // Witness < Memory < Setup inputs, then VirtualSetup < Cached (their heap slots).
            let (n, fs_copy, ex_copy) = if i > 0 {
                let n = previous_input_count;
                let final_inner: Vec<usize> = (0..n).filter(|o| !extra_set.contains(o)).collect();
                let mut extras = cache_dep_offsets.clone();
                extras.sort_unstable();
                extras.dedup();
                let cached: Vec<usize> = (0..cached_count).collect();
                (
                    n,
                    format!("{}{}", cd_ranges(&final_inner), cache_reads(&cached)),
                    cd_ranges(&extras),
                )
            } else {
                let (num_mem, num_wit, num_setup, l0_cachevars) = layer0_group_widths;
                let n = num_mem + num_wit + num_setup;
                let (wit_lo, wit_hi) = (num_mem, num_mem + num_wit);
                let (set_lo, set_hi) = (wit_hi, n);
                let g_fin = |lo: usize, hi: usize| -> Vec<usize> {
                    (lo..hi).filter(|o| !extra_set.contains(o)).collect()
                };
                let g_ext = |lo: usize, hi: usize| -> Vec<usize> {
                    (lo..hi).filter(|o| extra_set.contains(o)).collect()
                };
                let vsetup: Vec<usize> = (0..injected_virtualpoly_relations.len())
                    .map(|vp| l0_cachevars + vp)
                    .collect();
                let cached: Vec<usize> = (0..cached_count).collect();
                let fs = format!(
                    "{}{}{}{}{}",
                    cd_ranges(&g_fin(wit_lo, wit_hi)),
                    cd_ranges(&g_fin(0, num_mem)),
                    cd_ranges(&g_fin(set_lo, set_hi)),
                    cache_reads(&vsetup),
                    cache_reads(&cached)
                );
                let ex = format!(
                    "{}{}{}",
                    cd_ranges(&g_ext(wit_lo, wit_hi)),
                    cd_ranges(&g_ext(0, num_mem)),
                    cd_ranges(&g_ext(set_lo, set_hi))
                );
                (n, fs, ex)
            };
            format!(
                "{{
            let base := mload(CIRCUIT_PTR)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            let bp := add(GKR_ABS_PTR(), 32)
            // absorb final_step ++ extras contiguously, then draw (soundness: batching depends on
            // the extra cache-dependency evals). ONE keccak of [seed || final_step || extras].
{fs_copy}{ex_copy}            let s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR()))
            mstore(SEED_PTR(), s)
            s := keccak256(SEED_PTR(), 32)
            mstore(SEED_PTR(), s)
            next_alpha := mod(shr(128, s), P)
            next_ptr := add(ptr, mul(16, {n}))
            next_claim := 0
            }}"
            )
        } else {
            format!("next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, {previous_input_count})")
        };

        let check = if DEBUG_ENABLE_DUMMY_CHECKS {
            yul_format!(
                "
            let dummy_check := mod(add(claim, sub(P, rhs_scaled)), P)
            \tmstore(GKR_CIRCUIT_CACHE_PTR(), dummy_check)
            "
            )
        } else {
            yul_format!(
                "
            if mod(add(claim, sub(P, rhs_scaled)), P) {{ revert(0, 0) }}
            "
            )
        };
        yul_println!(
            "
            let rhs_scaled := mulmod(acc, eq_scale, P)
            // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
            // after stack-heavy values are dead
            {check:x}
            {writeback}
            // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
            // absorb final_step ++ extras in one keccak, THEN draw). next_claim unused (sccl recomputes).
            {claims_batch}
        }}
        "
        );

        // Emit the buffered gate sub-functions at TOP LEVEL (siblings of the layer function,
        // so their ptr/alpha params don't shadow). Hoisting lets the layer call them above.
        {
            let mut out = yul_main_output().lock().unwrap();
            out.push_str(&layer_cache_func);
            if !layer_chunk_funcs.is_empty() {
                out.push_str(&layer_chunk_funcs);
            }
            // compute_claim function (top-level, hoisted — the layer header calls it).
            out.push_str(&sccl_func);
        }

        // if i <= 1 {
        //     break
        // }
    }

    // INTRODUCE EXTERNAL HELPER FNS
    // GREAT FOR BYTECODE REDUCTION!!
    let check = if DEBUG_ENABLE_DUMMY_CHECKS {
        yul_format!(
            "
        let dummy_check := mod(add(claim, sub(P, g0g1_scaled)), P)
        \t\tmstore(GKR_CIRCUIT_CACHE_PTR(), dummy_check)
        "
        )
    } else {
        yul_format!(
            "
        if mod(add(claim, sub(P, g0g1_scaled)), P) {{ revert(0, 0) }}
        "
        )
    };
    let gate_calldataload_inner = Yul::calldataload(&123).0.replace("123", "idx");
    let gate_mload_inner = Yul::mload(&123).0.replace("123", "idx");
    yul_println!("
        function sumcheck_rounds_circuit(ptr, claim) -> next_ptr, next_claim, eq_scale {{
            // NB: need to inline __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS unfortunately
            eq_scale := 1
            let modulus := mload(P_PTR) // hoisted: DUP per use instead of re-mload every round
            for {{ let i := 0 }} lt(i, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS) {{ i := add(i, 1) }} {{
                let w0 := calldataload(ptr)
                let w1 := calldataload(add(ptr, 32))
                let c0 := shr(128, w0)
                let c1 := and(w0, MASK)
                let c2 := shr(128, w1)
                let c3 := and(w1, MASK)
                let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, modulus)
                let r := transcript_4to1_dual(w0, w1, modulus) // before-check draw is intentional; see HEURISTICS.md
                // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
                if mod(add(claim, sub(modulus, g0g1_scaled)), modulus) {{ revert(0, 0) }}
                claim := add(mulmod(add(mulmod(add(mulmod(c3, r, modulus), c2), r, modulus), c1), r, modulus), c0)
                let z := mload(add(POINT_PTR(), mul(i, 32)))
                let zr := mulmod(z, r, modulus)
                eq_scale := add(add(add(zr, zr), 1), sub(mul(4, modulus), add(z, r)))
                mstore(add(POINT_PTR(), mul(i, 32)), r)
                ptr := add(ptr, 64)
            }}
            next_ptr := ptr
            next_claim := claim
        }}
        function transcriptNto1(ptr, input_elements) -> alpha {{
            let input_bytes := mul(input_elements, 16)
            calldatacopy(add(SEED_PTR(), 32), ptr, input_bytes)
            let seed := keccak256(SEED_PTR(), add(32, input_bytes)) // absorb evals
            mstore(SEED_PTR(), seed)
            seed := keccak256(SEED_PTR(), 32)                       // draw (the mirror draws a fresh el)
            mstore(SEED_PTR(), seed)
            alpha := mod(shr(128, seed), P)                         // batching is a field element mod P
        }}
        function sumcheck_claims_batch(ptr, points) -> next_ptr, next_claim, next_alpha {{
            let is_odd := mod(points, 2)
            if is_odd {{
                next_claim := shr(128, calldataload(add(ptr, mul(16, sub(points, 1)))))
            }}
            next_alpha := transcriptNto1(ptr, points)
            let even_points := sub(points, is_odd)
            let pairs := shr(1, even_points)
            for {{ let pair := sub(pairs, 1) }} lt(pair, pairs) {{ pair := sub(pair, 1) }} {{
                let word := calldataload(add(ptr, mul(pair, 32)))
                let el1 := and(MASK, word)
                let el0 := shr(128, word)
                next_claim := add(mulmod(next_claim, next_alpha, P), el1)
                next_claim := add(mulmod(next_claim, next_alpha, P), el0)
            }}
            next_ptr := add(ptr, mul(16, points))
        }}

        function gkr_memrel_compress(address_space, addr_low, addr_high, ts_low, ts_high, val_low, val_high) -> compressed {{
            compressed := add(mload(add(MEMORY_CHALLS_PTR(), 192)), address_space)
            compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR()), addr_low, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 32)), addr_high, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 64)), ts_low, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 96)), ts_high, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 128)), val_low, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 160)), val_high, P))
        }}

        // Fold five generic lookup tuple columns into an existing Horner accumulator.
        // A single helper that took all c0..c9 made solc materialize all ten columns
        // at the call boundary and failed stack allocation. Splitting the fold into
        // two five-column calls keeps each call boundary small while still supporting
        // arbitrary linrel_to_calldata_inner() output for every column.
        function gkr_lookrel_compress_half(acc, c0, c1, c2, c3, c4) -> acc_next {{
            acc_next := add(mulmod(acc, mload(LOGUP_CHALLS_PTR()), P), c4)
            acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c3)
            acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c2)
            acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c1)
            acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c0)
        }}
        // One β-Horner step: acc·β + c. Callers chain ten of these (see lookrel_horner)
        // instead of one 5-arg compress_half, keeping every call boundary at 2 args so the
        // enclosing cache/gate function stays inside the EVM stack limit.
        function gkr_lookrel_step(acc, c) -> acc_next {{
            acc_next := add(mulmod(acc, mload(LOGUP_CHALLS_PTR()), P), c)
        }}

        // Split memrel into a 3-arg low + 4-arg high, composed by the caller as
        // add(low(...), high(...)). A single 7-arg gkr_memrel_compress forced solc to
        // materialize all 7 expression-args at the call boundary, running the enclosing
        // cache function 1 slot too deep (same failure the lookrel split above avoids).
        function gkr_memrel_compress_low(address_space, addr_low, addr_high) -> compressed {{
            compressed := add(mload(add(MEMORY_CHALLS_PTR(), 192)), address_space)
            compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR()), addr_low, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 32)), addr_high, P))
        }}
        function gkr_memrel_compress_high(ts_low, ts_high, val_low, val_high) -> compressed {{
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 64)), ts_low, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 96)), ts_high, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 128)), val_low, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 160)), val_high, P))
        }}
        // Reads one inits/teardowns `top_bits` u32 from the transcript preimage (little-endian,
        // at absolute calldata `byteoff`). These are the RAM-set base chunk indices absorbed into
        // Fiat-Shamir, so a mismatching value breaks the transcript — safe to read from calldata.
        function gkr_inits_teardowns_topbits(byteoff) -> v {{
            let w := calldataload(byteoff)
            v := add(add(byte(0, w), shl(8, byte(1, w))), add(shl(16, byte(2, w)), shl(24, byte(3, w))))
        }}

        function gkr_virtual_poly_compose_vars(len, skip) -> eval {{
            // let total := add(skip, len)
            let max := sub(__TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS, skip) // exclusive
            let min := sub(max, len)
            // NO NEED FOR THIS CHECK, WE DO IT VIA RUST
            // if gt(total, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS) {{ // abort when bad
            //     min := max
            // }}
            for {{ let i := min }} lt(i, max) {{ i := add(i, 1) }} {{
                eval := add(mul(eval, 2), mload(add(POINT_PTR(), mul(i, 32))))
            }}
        }}
        function gkr_virtual_poly_zero_vars(len) -> eval {{
            eval := 1
            for {{ let i := 0 }} lt(i, len) {{ i := add(i, 1) }} {{
                eval := mulmod(eval, add(1, sub(mul(2, P), mload(add(POINT_PTR(), mul(i, 32))))), P)
            }}
        }}
        function gkr_virtual_poly_rangecheck(width) -> eval {{
            eval := mulmod(gkr_virtual_poly_compose_vars(width, 0), gkr_virtual_poly_zero_vars(sub(__TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS, width)), P)
        }}

        function gate_calldataload(idx) -> load {{
            load := {gate_calldataload_inner}
        }}
        function gate_mload(idx) -> load {{
            load := {gate_mload_inner}
        }}
        function pointcheck_update(acc, alpha, gate) -> next_acc {{
            next_acc := add(mulmod(acc, alpha, P), gate)
        }}
        function logup_pointcheck_update(acc, alpha, num_out, den_out) -> next_acc {{
            acc := pointcheck_update(acc, alpha, den_out)
            next_acc := pointcheck_update(acc, alpha, num_out)
        }}
        function u128_neg(input) -> neg_input {{
            neg_input := sub(mul(2, P), input)
        }}

        // 3
        function gate_aggregatelookuprationalpair(alpha, acc, num1_idx, num2_idx, den1_idx, den2_idx) -> next_acc {{
            let num1 := gate_calldataload(num1_idx)
            let num2 := gate_calldataload(num2_idx)
            let den1 := gate_calldataload(den1_idx)
            let den2 := gate_calldataload(den2_idx)
            let den_out := mulmod(den1, den2, P)
            let num_out := add(mulmod(num1, den2, P), mulmod(num2, den1, P))
            next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
        }}
        function gate_copyinextensionfield(alpha, acc, input_idx) -> next_acc {{
            let input := gate_calldataload(input_idx)
            next_acc := pointcheck_update(acc, alpha, input)
        }}

        // 2
        function gate_maskintoidentityproduct(alpha, acc, input_idx, mask_idx) -> next_acc {{
            let input := gate_calldataload(input_idx)
            let mask := gate_calldataload(mask_idx)
            // let neg_mask := u128_neg(mask)
            // let gate := add(mulmod(input, mask, P), add(1, neg_mask))
            let neg_one := sub(P, 1)
            let gate := add(mulmod(mask, add(input, neg_one), P), 1)
            next_acc := pointcheck_update(acc, alpha, gate)
        }}
    ");
    let _ = DEBUG_ENABLE_DUMMY_CHECKS;
    let out = std::mem::take(&mut *yul_main_output().lock().unwrap());
    // Modulus representation: the ~124-bit Proth120 P as a Solidity `constant` compiles to a
    // PUSH16 rematerialized at EVERY mulmod/addmod/sub — ~1000+ times across the layer-0 gates,
    // several KB of pure constant-push. P is already mirrored at the fixed heap slot P_PTR, so
    // read it with `mload(P_PTR)` (PUSH1 + MLOAD, consumed immediately — no live stack slot, so
    // no "stack too deep" in the deep gate sequences). Purely a size win; runtime value identical.
    out.replace(", P)", ", mload(P_PTR))")
        .replace("sub(P, ", "sub(mload(P_PTR), ")
}
