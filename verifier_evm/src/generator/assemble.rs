//! Assemble full verifier Solidity from the circuit artifact + caller-supplied params.
//!
//! The GKR verifier is the hand-written `gkr.sol` template with the circuit-specific
//! `circuit.yul` inlined at `// __INLINE_CIRCUIT_YUL__` and its circuit-derived `constant`s
//! substituted. Everything the generator needs about the *circuit* comes from the artifact;
//! the two genuinely non-circuit values (PoW difficulty, program terminal PC) are parameters.
//!
//! The WHIR *proving-config* (fold/query/PoW schedule, base rate, merkle cap) is not encoded in
//! the circuit artifact; it is supplied by the caller as the same `ProverConfig` the prover used,
//! and (with `pack_log2`) drives both halves of the merged verifier so they stay consistent — see [`WhirGenConfig`].

use super::whir::WhirGenConfig;
use super::emit_circuit_yul;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::gkr::prover_config::ProverConfig;

const GKR_TEMPLATE: &str = include_str!("../templates/gkr.sol");
const WHIR_TEMPLATE: &str = include_str!("../templates/whir.sol");

/// Marker in `gkr.sol` where the generated `circuit.yul` is spliced.
const INLINE_MARKER: &str = "// __INLINE_CIRCUIT_YUL__";

/// Marker in `gkr.sol`'s `gkr_dr_final` where the boundary-layer LSB reorder (SI) is generated.
const SI_MARKER: &str = "                // __GKR_BOUNDARY_SI__";

/// Marker in `gkr.sol`'s `gkr_circuit` where the per-layer sumcheck calls are generated.
const CIRCUIT_LAYER_CALLS_MARKER: &str = "            // __GKR_CIRCUIT_LAYER_CALLS__";

/// Emit the `gkr_circuit` body: one `sumcheck_circuit_layer{i}` call per circuit layer, from
/// the output layer (highest index — reads the dim-reduce output `GKR_CLAIMS_PTR`) down to
/// layer 0. Generated from the artifact's layer count so the driver can't drift out of sync
/// with the emitted `sumcheck_circuit_layer{i}` functions when the circuit changes depth.
fn gkr_circuit_layer_calls(circuit: &GKRCircuitArtifact<Proth120>) -> String {
    let n = circuit.layers.len();
    assert!(n > 0, "circuit must have at least one layer");
    (0..n)
        .rev()
        .map(|i| {
            format!(
                "            ptr, claim,\n            alpha := sumcheck_circuit_layer{i}(ptr, claim, alpha)\n"
            )
        })
        .collect()
}

/// Emit the boundary-layer `SI` reorder as `mstore(add(SI, 32*i), offset)` lines. `SI[logical] =
/// offset` = the artifact's `global_output_map` value offsets flattened in iteration
/// (`BTreeMap<OutputType>`) order — the permutation from offset-stored LSB lines to logical
/// (OutputType-group) order, so grand-products land at logical slots 0,1,8,9.
fn boundary_si_yul(circuit: &GKRCircuitArtifact<Proth120>) -> String {
    let offsets: Vec<usize> = circuit
        .global_output_map
        .values()
        .flatten()
        .map(|addr| match addr {
            GKRAddress::InnerLayer { offset, .. } => *offset,
            other => panic!("unexpected output address {other:?} in global_output_map"),
        })
        .collect();
    assert_eq!(
        offsets.len(),
        10,
        "gkr_dr_final expects 10 GKR output LSB lines, got {}",
        offsets.len()
    );
    offsets
        .iter()
        .enumerate()
        .map(|(i, off)| format!("                mstore(add(SI, {}), {off})\n", i * 32))
        .collect()
}

/// First free memory offset past whir.sol's static region map (the drawn-
/// query scratch `DRAW_BUF_PTR = 30016` + up to 50 slots, rounded up): the
/// generator places the schedule-sized final-round regions from here.
const WHIR_FINAL_SCRATCH_BASE: u128 = 31680;

/// Replace the RHS of the single `uint256 constant <name> = <...>;` (or
/// `address constant <name> = <...>;`) line with `= <value>;`, preserving
/// indentation and any trailing `// comment`. Panics unless exactly one such
/// line exists, so a template rename can never silently drop a substitution.
fn set_const(src: &str, name: &str, value: impl std::fmt::Display) -> String {
    let needle = format!("constant {name} "); // name is followed by alignment whitespace then '='
    let mut hits = 0usize;
    let body: Vec<String> = src
        .lines()
        .map(|line| {
            let is_const_line = {
                let t = line.trim_start();
                t.starts_with("uint256 constant ") || t.starts_with("address constant ")
            };
            if is_const_line && line.contains(&needle) {
                if let Some(eq) = line.find('=') {
                    if let Some(rel) = line[eq..].find(';') {
                        let semi = eq + rel;
                        hits += 1;
                        return format!("{}= {}{}", &line[..eq], value, &line[semi..]);
                    }
                }
            }
            line.to_string()
        })
        .collect();
    assert_eq!(
        hits, 1,
        "expected exactly one `uint256/address constant {name}` line in the template"
    );
    let mut out = body.join("\n");
    if src.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// Keep everything up to (not including) the first line that starts a contract named `marker`,
/// dropping the trailing test/bench harness contracts so the generated source is just the
/// production verifier. Also trims a trailing block-comment that introduces the removed section.
fn strip_from_contract(src: &str, marker: &str) -> String {
    let needle = format!("contract {marker}");
    let cut = src
        .find(&needle)
        .unwrap_or_else(|| panic!("template missing `{needle}`"));
    // back up over any immediately-preceding `//`-comment lines that document the removed section
    let mut end = src[..cut].trim_end_matches([' ', '\t']).len();
    end = src[..end].trim_end_matches('\n').len();
    loop {
        let line_start = src[..end].rfind('\n').map(|i| i + 1).unwrap_or(0);
        if src[line_start..end].trim_start().starts_with("//") {
            end = src[..line_start].trim_end_matches('\n').len();
        } else {
            break;
        }
    }
    let mut out = src[..end].to_string();
    out.push('\n');
    out
}

/// Circuit-derived layout values used to substitute the gkr.sol constants.
struct Derived {
    rounds: u128,
    num_memwit: u128,
    num_setup: u128,
    merged_mw: u128,
    num_teardown_sets: u128,
}

impl Derived {
    fn from(circuit: &GKRCircuitArtifact<Proth120>) -> Self {
        assert!(circuit.trace_len.is_power_of_two() && circuit.trace_len > 0);
        let rounds = circuit.trace_len.trailing_zeros() as u128;
        let num_memwit =
            (circuit.memory_layout.total_width + circuit.witness_layout.total_width) as u128;
        Self {
            rounds,
            num_memwit,
            num_setup: circuit.generic_lookup_tables_width as u128,
            merged_mw: num_memwit.div_ceil(16),
            num_teardown_sets: circuit.memory_layout.teardown_sets.len() as u128,
        }
    }
}

/// Generate the merged `GkrWhirVerifier` Solidity source for `circuit`: GKR and WHIR verified
/// in ONE transaction, the GKR→WHIR handoff state passed in memory.
///
/// The circuit *layout* comes from the artifact; the WHIR *proving config* (fold/query/PoW
/// schedule, base rate, merkle cap) comes from `prover_config`, and the base-layer packing factor
/// from `pack_log2` (the GKR `CommitmentMode`). Deriving both halves from the same config is
/// what guarantees GKR↔WHIR consistency. `external_pow_bits` / `whir_batch_pow_bits` are the two
/// per-circuit PoW difficulties (not part of the WHIR schedule), and `final_pc` the program's
/// terminal PC.
pub fn generate_verifier(
    circuit: &GKRCircuitArtifact<Proth120>,
    prover_config: &ProverConfig,
    pack_log2: usize,
    external_pow_bits: u32,
    whir_batch_pow_bits: u32,
    final_pc: u32,
) -> String {
    let d = Derived::from(circuit);
    // WHIR config derived from the same source the prover used, plus the artifact's widths.
    let wc = WhirGenConfig::derive(
        &prover_config.whir_schedule,
        pack_log2,
        d.rounds as usize,
        d.num_memwit as usize,
        d.num_setup as usize,
    );
    // GKR↔WHIR consistency: the shared parameters must agree between the two verifiers.
    assert_eq!(
        wc.merged_mw as u128, d.merged_mw,
        "GKR/WHIR merged mem+wit width disagree ({} vs {})",
        wc.merged_mw, d.merged_mw
    );
    assert!(pack_log2 > 0, "pack_log2 must be positive");

    let cap = wc.cap_size as u128;
    // registers + final_pc/ts + top_bits(num_teardown_sets * 4) + setup_cap + memory_cap
    let preimage_bytes =
        super::PREIMAGE_TOP_BITS_BYTE_OFFSET as u128 + d.num_teardown_sets * 4 + 2 * cap * 32;
    let caps_bytes = 2 * cap * 32;

    // 1. GKR verifier: inline circuit.yul (replace the whole marker line, matching the awk
    //    splice the shell scripts used), then substitute circuit-derived + param constants.
    let circuit_yul = emit_circuit_yul(circuit);
    let mut gkr = String::with_capacity(GKR_TEMPLATE.len() + circuit_yul.len());
    let mut inlined = false;
    for line in GKR_TEMPLATE.lines() {
        if line.contains(INLINE_MARKER) {
            gkr.push_str(circuit_yul.trim_end_matches('\n'));
            gkr.push('\n');
            inlined = true;
        } else {
            gkr.push_str(line);
            gkr.push('\n');
        }
    }
    assert!(inlined, "gkr.sol template missing inline marker");
    for (name, value) in [
        ("__TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS", d.rounds),
        ("__TEMPLATE_WHIR_NUM_MEMWIT", d.num_memwit),
        ("__TEMPLATE_WHIR_NUM_SETUP", d.num_setup),
        ("__TEMPLATE_WHIR_MERGED_MW", wc.merged_mw as u128),
        ("__TEMPLATE_WHIR_PACK_LOG2", pack_log2 as u128),
        ("__TEMPLATE_WHIR_Z_COORDS", d.rounds + pack_log2 as u128),
        ("__TEMPLATE_WHIR_BASE_Z_COORDS", d.rounds),
        ("__TEMPLATE_WHIR_CAP", cap),
        ("__TEMPLATE_MERKLE_TREE_CAPS_BYTES", caps_bytes),
        ("__TEMPLATE_GKR_INIT_PREIMAGE_BYTES", preimage_bytes),
        ("__TEMPLATE_EXTERNAL_POW_BITS", external_pow_bits as u128),
        (
            "__TEMPLATE_WHIR_BATCH_POW_BITS",
            whir_batch_pow_bits as u128,
        ),
        ("__TEMPLATE_EXPECTED_FINAL_PC", final_pc as u128),
    ] {
        gkr = set_const(&gkr, name, value);
    }

    // Boundary-layer LSB reorder for gkr_dr_final: the dim-reduce LSB lines are stored in
    // GKRAddress-offset order, but the g-accumulator wants OutputType-group (iteration) order so
    // grand-products land at logical slots 0,1,8,9. `SI[logical] = offset` = the artifact's
    // global_output_map value offsets flattened in iteration (BTreeMap<OutputType>) order.
    let gkr = gkr.replace(&format!("{SI_MARKER}\n"), &boundary_si_yul(circuit));

    // Circuit-layer sumcheck driver: generate the per-layer call sequence so `gkr_circuit`
    // always runs exactly the layers the artifact defines (output layer first, down to 0).
    let gkr = gkr.replace(
        &format!("{CIRCUIT_LAYER_CALLS_MARKER}\n"),
        &gkr_circuit_layer_calls(circuit),
    );
    assert!(
        !gkr.contains("__GKR_CIRCUIT_LAYER_CALLS__"),
        "gkr.sol template missing the circuit-layer-calls marker"
    );

    // Drop the trailing test/bench harness (GKRVerifierTest + the via_ir-only GKRStreamGen) so
    // the production source is just `contract GKRVerifier` and compiles under the legacy backend.
    let gkr = strip_from_contract(&gkr, "GKRVerifierTest");

    // 2. WHIR verifier: inject the per-round fold/query/PoW schedule generated from `wc`, then
    //    substitute every config-derived constant (schedule count, cap, RS-codeword domain
    //    generators, base-column geometry). Nothing WHIR-specific is hand-supplied anymore.
    let whir_schedule_yul = wc.schedule_switch_yul();
    let mut whir = WHIR_TEMPLATE.replace(
        "            // __WHIR_SCHEDULE_SWITCH__",
        whir_schedule_yul.trim_end_matches('\n'),
    );
    assert!(
        !whir.contains("__WHIR_SCHEDULE_SWITCH__"),
        "whir.sol template missing the schedule marker"
    );
    for (name, value) in [
        ("CAP", cap),
        ("CAP_LOG2", wc.cap_log2 as u128),
        ("__TEMPLATE_WHIR_NUM_ROUNDS", wc.num_rounds as u128),
        ("__TEMPLATE_WHIR_GEN", wc.gen),
        ("__TEMPLATE_WHIR_GEN_INV", wc.gen_inv),
        ("__TEMPLATE_WHIR_NZ", wc.nz as u128),
        ("__TEMPLATE_WHIR_GCOUNT", wc.gcount as u128),
        ("__TEMPLATE_WHIR_RFIN", wc.rfin as u128),
        ("__TEMPLATE_WHIR_NBCAPS", wc.nbcaps as u128),
        ("__TEMPLATE_WHIR_MERGED_MW", wc.merged_mw as u128),
        ("__TEMPLATE_WHIR_SETUP_MERGED", wc.setup_merged as u128),
        // Final-round scratch layout, derived from the schedule's plain-text
        // tail size (2^rfin monomials, one 32-byte word each): the monomial
        // region starts past the static map and the absorb/halving-fold
        // scratch follows it.
        ("__TEMPLATE_WHIR_MONO_PTR", WHIR_FINAL_SCRATCH_BASE),
        (
            "__TEMPLATE_WHIR_FEVAL_PTR",
            WHIR_FINAL_SCRATCH_BASE + (1u128 << wc.rfin) * 32,
        ),
    ] {
        whir = set_const(&whir, name, value);
    }

    // 3. Splice the WHIR half into the GKR contract: one Solidity source, one transaction.
    let gkr = set_const(&gkr, "__TEMPLATE_VERIFIED_TOPIC", verified_event_topic());
    build_merged(&gkr, &whir)
}

// ── Splicing the WHIR half into the GKR contract ────────────────────────────────────────────
//
// whir.sol is a template FRAGMENT: its Yul (the helper functions + `whir_verify(cd_start)`) is
// inlined into the GKR template's single `assembly ("memory-safe")` block, where the GKR half's
// `emit_gkr_mark` writes the GKR→WHIR handoff state straight into the WHIR memory regions and
// the fallback tail calls `whir_verify`. What the splice has to respect:
//  * one Yul block → no name clashes: every WHIR Solidity constant is prefixed `W_` (the GKR
//    template has a `SEED_PTR()` *function*, whir.sol a `SEED_PTR` *constant*); `P`, `MASK` and
//    `__TEMPLATE_WHIR_MERGED_MW` are shared (identical values) and come from the GKR side. The
//    Yul function names were checked disjoint (whir: batch_oracle, do_*, draw*, fold_*, ...).
//  * memory-safe assembly: via_ir spills into [0x80, MINIMUM_FREE_HEAP_PTR) and the GKR heap
//    occupies [MINIMUM_FREE_HEAP_PTR, ~25 KB) (GKR_QTABLE_PTR = SEED+420·32 ≈ 22.1 KB plus the
//    ~3 KB table), so every WHIR memory region is relocated by MERGED_WHIR_MEM_BASE, above both;
//    the WHIR half never touches 0x40/0x60, and the end-of-fallback spill guard is re-checked
//    after it.
const MERGED_WHIR_MEM_BASE: u128 = 32768;

/// whir.sol constants that are memory addresses (relocated by MERGED_WHIR_MEM_BASE).
const WHIR_MEM_CONSTS: &[&str] = &[
    "SEED_PTR",
    "Z_PTR",
    "ACC_PREF_PTR",
    "POW_PTR",
    "GAMMA_PTR",
    "FOLD_CH_PTR",
    "HPO_PTR",
    "FBUF_PTR",
    "LEAF_PTR",
    "REG_CD",
    "REG_CLAIM",
    "REG_NUMPOW",
    "REG_ZIOFF",
    "REG_CC",
    "REG_CURDELIN",
    "BCAP0_PTR",
    "BCAP1_PTR",
    "QCAP_PTR",
    "NCAP_PTR",
    "QIDX_BUF_PTR",
    "DRAW_BUF_PTR",
    "HANDOFF_BATCHING_PTR",
    "PUB_PTR",
    "SETUP_PTR",
    "__TEMPLATE_WHIR_MONO_PTR",
    "__TEMPLATE_WHIR_FEVAL_PTR",
];
/// whir.sol constants the GKR template already declares with the same value — not re-declared.
const WHIR_SHARED_CONSTS: &[&str] = &["__TEMPLATE_WHIR_MERGED_MW"];
/// `W_*` names the GKR template references (handoff + Verified event) — must come from whir.sol.
const GKR_REQUIRED_WHIR_CONSTS: &[&str] = &[
    "W_SEED_PTR",
    "W_HANDOFF_BATCHING_PTR",
    "W_REG_CLAIM",
    "W_Z_PTR",
    "W_BCAP0_PTR",
    "W_BCAP1_PTR",
    "W_PUB_PTR",
    "W_SETUP_PTR",
    "W_LEAF_PTR",
];

fn is_ident_char(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

/// Replace whole-identifier occurrences of `from` with `to`.
fn rename_ident(text: &str, from: &str, to: &str) -> String {
    let b = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    while i < text.len() {
        if text[i..].starts_with(from) {
            let after = i + from.len();
            let before_ok = i == 0 || !is_ident_char(b[i - 1]);
            let after_ok = after >= text.len() || !is_ident_char(b[after]);
            if before_ok && after_ok {
                out.push_str(to);
                i = after;
                continue;
            }
        }
        let ch = text[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

fn line_idx(lines: &[&str], needle: &str, what: &str) -> usize {
    lines
        .iter()
        .position(|l| l.contains(needle))
        .unwrap_or_else(|| panic!("whir.sol template: missing {what} anchor (`{needle}`)"))
}

/// keccak256("Verified(bytes32,bytes32)") as a 0x-prefixed hex literal (the event's topic0).
fn verified_event_topic() -> String {
    use sha3::Digest;
    let d = sha3::Keccak256::digest(b"Verified(bytes32,bytes32)");
    let mut s = String::from("0x");
    for byte in d.iter() {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}

/// Splice the (substituted) whir.sol fragment into the (substituted) GKR source.
fn build_merged(gkr: &str, whir: &str) -> String {
    let lines: Vec<&str> = whir.lines().collect();

    // 1. WHIR constants: the block `HALF` .. `FEVAL_PTR` (P / MASK precede HALF; shared with GKR).
    let cs = line_idx(&lines, "uint256 constant HALF", "constants start");
    let ce = line_idx(&lines, "uint256 constant FEVAL_PTR", "constants end");
    let mut consts = String::new();
    let mut names: Vec<String> = Vec::new();
    for &line in &lines[cs..=ce] {
        let t = line.trim_start();
        let name = t.strip_prefix("uint256 constant ").map(|rest| {
            rest.split(|c: char| c.is_whitespace() || c == '=')
                .next()
                .unwrap()
                .to_string()
        });
        let Some(name) = name else {
            consts.push_str(line);
            consts.push('\n');
            continue;
        };
        if WHIR_SHARED_CONSTS.contains(&name.as_str()) {
            continue;
        }
        if WHIR_MEM_CONSTS.contains(&name.as_str()) {
            let eq = line.find('=').unwrap();
            let semi = eq + line[eq..].find(';').unwrap();
            let lit = line[eq + 1..semi].trim();
            let v: u128 = lit
                .parse()
                .unwrap_or_else(|_| panic!("whir const {name} is not a decimal literal: `{lit}`"));
            consts.push_str(&format!(
                "{}= {}{}\n",
                &line[..eq],
                v + MERGED_WHIR_MEM_BASE,
                &line[semi..]
            ));
        } else {
            consts.push_str(line);
            consts.push('\n');
        }
        names.push(name);
    }
    for n in WHIR_MEM_CONSTS {
        assert!(
            names.iter().any(|x| x == n),
            "whir.sol template: memory constant {n} not found in the constants block"
        );
    }

    // 2. the Yul: everything between the assembly open and the end marker (helper functions +
    //    `whir_verify(cd_start)`, both already in the shape the merged contract needs).
    let asm_open = line_idx(&lines, "        assembly {", "assembly block");
    let yul_end = line_idx(&lines, "// __WHIR_YUL_END__", "Yul end marker");
    assert!(asm_open < yul_end, "whir.sol template: Yul end marker precedes the assembly block");
    let mut whir_yul = lines[asm_open + 1..yul_end].join("\n");
    whir_yul.push('\n');

    // 3. prefix every WHIR constant so nothing collides with the GKR template's names
    for n in &names {
        let to = format!("W_{n}");
        consts = rename_ident(&consts, n, &to);
        whir_yul = rename_ident(&whir_yul, n, &to);
    }

    // 4. splice into the GKR source
    let out = gkr.replace("    // __WHIR_CONSTANTS__", consts.trim_end_matches('\n'));
    let out = out.replace("        // __WHIR_INLINE__", &whir_yul);
    for leftover in [
        "__WHIR_CONSTANTS__",
        "__WHIR_INLINE__",
        "__WHIR_YUL_END__",
        "COMMIT_PTR",
        "MARK_WHIR_SELECTOR",
        "MARK_GKR_SELECTOR",
        "__TEMPLATE_REGISTRY_ADDRESS",
    ] {
        assert!(!out.contains(leftover), "merged source still contains `{leftover}`");
    }
    for req in GKR_REQUIRED_WHIR_CONSTS {
        assert!(
            out.contains(&format!("constant {req} ")),
            "the GKR template references {req} but whir.sol did not provide it"
        );
    }
    out
}
