//! Assemble the merged verifier Solidity from the circuit artifact + caller-supplied params.
//!
//! The GKR verifier is the hand-written `gkr.sol` template with the circuit-specific
//! `circuit.yul` inlined at `// __INLINE_CIRCUIT_YUL__` and the WHIR fragment (`whir.sol`)
//! spliced in; EVERY `__TEMPLATE_*` constant of both templates is assigned here. The rule the
//! templates follow: anything the compiled circuit or the prover config is the source of truth
//! for — widths, output counts, cap size, preimage offsets, the whole heap map — is referenced
//! by its `__TEMPLATE_*` NAME in the Solidity/Yul and gets its literal value from this file
//! (inline assembly can only consume literal constants, so the literal lives in the
//! declaration alone). The few genuinely non-circuit deployment values (PoW difficulties, the
//! program's terminal PC, the inits/teardowns top bits) are parameters of [`generate_verifier`].
//!
//! The WHIR *proving-config* (fold/query/PoW schedule, base rate, merkle cap) is not encoded in
//! the circuit artifact; it is supplied by the caller as the same `ProverConfig` the prover used,
//! and (with `pack_log2`) drives both halves of the merged verifier so they stay consistent — see
//! [`WhirGenConfig`].

use super::whir::WhirGenConfig;
use super::{emit_circuit_yul_with_stats, CircuitYulStats, Lit};
use cs::definitions::{GKRAddress, OutputType};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::gkr::prover_config::ProverConfig;
use std::collections::BTreeSet;

const GKR_TEMPLATE: &str = include_str!("../templates/gkr.sol");
const WHIR_TEMPLATE: &str = include_str!("../templates/whir.sol");

/// Marker in `gkr.sol` where the generated `circuit.yul` is spliced.
const INLINE_MARKER: &str = "// __INLINE_CIRCUIT_YUL__";

/// Marker in `gkr.sol`'s `gkr_dr_final` where the boundary-layer LSB reorder (SI) is generated.
const SI_MARKER: &str = "                // __GKR_BOUNDARY_SI__";

/// Marker in `gkr.sol`'s `gkr_circuit` where the per-layer sumcheck calls are generated.
const CIRCUIT_LAYER_CALLS_MARKER: &str = "            // __GKR_CIRCUIT_LAYER_CALLS__";

/// The GKR output-poly layout `gkr.sol` is written against (OutputType iteration order, two
/// lines each): Perm(0,1) · Lookup16(2,3) · LookupTs(4,5) · GenericLookup(6,7) · I&T(8,9).
/// gkr_init's permutation products (slots 0,1,8,9), check_lookup_identities' three (num, den)
/// pairs and gkr_dr_final's g-accumulator all assume it, so the generator refuses anything else.
const EXPECTED_OUTPUT_TYPES: [OutputType; 5] = [
    OutputType::PermutationProduct,
    OutputType::Lookup16Bits,
    OutputType::LookupTimestamps,
    OutputType::GenericLookup,
    OutputType::InitsAndTeardownsProduct,
];

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
fn boundary_si_yul(circuit: &GKRCircuitArtifact<Proth120>, num_outputs: usize) -> String {
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
        num_outputs,
        "gkr_dr_final expects {num_outputs} GKR output LSB lines, got {}",
        offsets.len()
    );
    offsets
        .iter()
        .enumerate()
        .map(|(i, off)| format!("                mstore(add(SI, {}), {off})\n", i * 32))
        .collect()
}

/// Is `line` a `uint256/uint8/address constant NAME ...;` declaration? Returns the name.
fn const_decl_name(line: &str) -> Option<&str> {
    let t = line.trim_start();
    let rest = t
        .strip_prefix("uint256 constant ")
        .or_else(|| t.strip_prefix("uint8 constant "))
        .or_else(|| t.strip_prefix("address constant "))?;
    rest.split(|c: char| c.is_whitespace() || c == '=').next()
}

/// Replace the RHS of the single `… constant <name> = <...>;` line with `= <value>;`,
/// preserving indentation and any trailing `// comment`. Panics unless exactly one such line
/// exists, so a template rename can never silently drop a substitution. Every name set this
/// way is recorded in `assigned` (the generator checks at the end that no `__TEMPLATE_*`
/// declaration was left unassigned).
fn set_const(
    src: &str,
    name: &str,
    value: impl std::fmt::Display,
    assigned: &mut BTreeSet<String>,
) -> String {
    let mut hits = 0usize;
    let body: Vec<String> = src
        .lines()
        .map(|line| {
            if const_decl_name(line) == Some(name) {
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
        "expected exactly one `constant {name}` declaration in the template"
    );
    assigned.insert(name.to_string());
    let mut out = body.join("\n");
    if src.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// The literal RHS of the single `… constant <name> = <literal>;` declaration (decimal or hex).
fn read_const(src: &str, name: &str) -> u128 {
    let mut found = None;
    for line in src.lines() {
        if const_decl_name(line) == Some(name) {
            let eq = line.find('=').unwrap();
            let semi = eq + line[eq..].find(';').unwrap();
            let lit = line[eq + 1..semi].trim();
            let v = if let Some(hex) = lit.strip_prefix("0x") {
                u128::from_str_radix(hex, 16)
            } else {
                lit.parse()
            }
            .unwrap_or_else(|_| panic!("template constant {name} is not a literal: `{lit}`"));
            assert!(found.is_none(), "template declares {name} more than once");
            found = Some(v);
        }
    }
    found.unwrap_or_else(|| panic!("template does not declare constant {name}"))
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
    rounds: usize,
    mem_width: usize,
    wit_width: usize,
    num_memwit: usize,
    num_setup: usize,
    merged_mw: usize,
    num_teardown_sets: usize,
    num_outputs: usize,
}

impl Derived {
    fn from(circuit: &GKRCircuitArtifact<Proth120>, pack_log2: usize) -> Self {
        assert!(circuit.trace_len.is_power_of_two() && circuit.trace_len > 0);
        let rounds = circuit.trace_len.trailing_zeros() as usize;
        let num_memwit = circuit.memory_layout.total_width + circuit.witness_layout.total_width;
        // the template's fixed output-poly layout (see EXPECTED_OUTPUT_TYPES)
        let keys: Vec<OutputType> = circuit.global_output_map.keys().copied().collect();
        assert_eq!(
            keys, EXPECTED_OUTPUT_TYPES,
            "gkr.sol is written for the output types {EXPECTED_OUTPUT_TYPES:?} (in this order)"
        );
        for (ty, addrs) in circuit.global_output_map.iter() {
            assert_eq!(addrs.len(), 2, "output type {ty:?} must have exactly 2 lines");
        }
        let num_outputs = circuit.global_output_map.values().map(Vec::len).sum();
        Self {
            rounds,
            mem_width: circuit.memory_layout.total_width,
            wit_width: circuit.witness_layout.total_width,
            num_memwit,
            num_setup: circuit.generic_lookup_tables_width,
            merged_mw: num_memwit.div_ceil(1 << pack_log2),
            num_teardown_sets: circuit.memory_layout.teardown_sets.len(),
            num_outputs,
        }
    }
}

/// Bump allocator for the hand-placed heap: regions are laid out back to back (each padded to
/// a whole number of 32-byte words, so a region's last word never overlaps the next region's
/// first) and the layout is recorded so the generated source documents it. The base itself is
/// whatever the template's spill-safe prefix ends at — the EVM needs no alignment.
struct HeapAlloc {
    next: u128,
    regions: Vec<(String, u128, Lit)>, // (name, start, size)
}

impl HeapAlloc {
    fn new(base: u128) -> Self {
        Self {
            next: base,
            regions: Vec::new(),
        }
    }
    /// Append a region; `size` is the region's padded size (a positive multiple of 32).
    fn region(&mut self, name: &str, size: &Lit) -> u128 {
        assert!(
            size.value > 0 && size.value.is_multiple_of(32),
            "heap region {name}: size {} = {} must be a positive multiple of 32",
            size.expr(),
            size.value
        );
        let start = self.next;
        self.next += size.value;
        self.regions.push((name.to_string(), start, size.clone()));
        start
    }
}

/// `32 * ceil(bytes / 32)` — a byte count rounded up to whole 32-byte words.
fn words_for(bytes: usize) -> Lit {
    Lit::words((bytes as u128).div_ceil(32))
}

/// Generate the merged `GkrWhirVerifier` Solidity source for `circuit`: GKR and WHIR verified
/// in ONE transaction, the GKR→WHIR handoff state passed in memory, the verified statement
/// reported to the constructor-pinned registry.
///
/// The circuit *layout* comes from the artifact; the WHIR *proving config* (fold/query/PoW
/// schedule, base rate, merkle cap) comes from `prover_config`, and the base-layer packing factor
/// from `pack_log2` (the GKR `CommitmentMode`). Deriving both halves from the same config is
/// what guarantees GKR↔WHIR consistency. The remaining parameters are deployment properties of
/// the *program* (never of a proof): `external_pow_bits` / `whir_batch_pow_bits` are the two
/// per-circuit PoW difficulties (not part of the WHIR schedule), `final_pc` the program's
/// terminal PC, and `inits_teardowns_top_bits` the RAM-set base chunk index of every
/// inits/teardowns set the circuit has (one per `memory_layout.teardown_sets` entry, each
/// fitting a byte) — the prover's preimage must carry exactly these values.
pub fn generate_verifier(
    circuit: &GKRCircuitArtifact<Proth120>,
    prover_config: &ProverConfig,
    pack_log2: usize,
    external_pow_bits: u32,
    whir_batch_pow_bits: u32,
    final_pc: u32,
    inits_teardowns_top_bits: &[u32],
) -> String {
    assert!(pack_log2 > 0, "pack_log2 must be positive");
    let d = Derived::from(circuit, pack_log2);
    assert_eq!(
        prover_config.trace_len_log2, d.rounds,
        "prover config trace_len_log2 {} != circuit trace log2 {}",
        prover_config.trace_len_log2, d.rounds
    );
    // WHIR config derived from the same source the prover used, plus the artifact's widths.
    let wc = WhirGenConfig::derive(
        &prover_config.whir_schedule,
        pack_log2,
        d.rounds,
        d.num_memwit,
        d.num_setup,
    );
    // GKR↔WHIR consistency: the shared parameters must agree between the two halves.
    assert_eq!(
        wc.merged_mw, d.merged_mw,
        "GKR/WHIR merged mem+wit width disagree ({} vs {})",
        wc.merged_mw, d.merged_mw
    );
    assert_eq!(
        wc.setup_merged, 1,
        "gkr.sol folds the setup columns into ONE merged claim (NUM_SETUP {} > PACK {})",
        d.num_setup,
        1usize << pack_log2
    );
    assert_eq!(
        prover_config.cap_size, prover_config.whir_schedule.cap_size,
        "the templates use one merkle cap size for the base oracles and the WHIR oracles"
    );
    let cap = wc.cap_size;

    // inits/teardowns top bits: one per RAM set the circuit has, each pinned as a uint8 constant
    assert_eq!(
        inits_teardowns_top_bits.len(),
        d.num_teardown_sets,
        "{} inits/teardowns top bits supplied, but the circuit has {} teardown sets",
        inits_teardowns_top_bits.len(),
        d.num_teardown_sets
    );
    assert_eq!(
        d.num_teardown_sets,
        super::NUM_INITS_TEARDOWNS_TOP_BITS,
        "gkr.sol pins {} __TEMPLATE_INITS_TEARDOWNS_TOP_BITS_ constants, the circuit has {} sets",
        super::NUM_INITS_TEARDOWNS_TOP_BITS,
        d.num_teardown_sets
    );
    for (i, &tb) in inits_teardowns_top_bits.iter().enumerate() {
        assert!(
            tb <= u8::MAX as u32,
            "inits/teardowns top bits [{i}] = {tb} does not fit a byte"
        );
    }

    // GKR entry geometry: the dimension reduction stops at the explicit output layer.
    let output_log2 = prover_config.sumcheck_explicit_output_size_log_2;
    assert!(
        output_log2 >= 1 && output_log2 < d.rounds,
        "sumcheck_explicit_output_size_log_2 {output_log2} out of range for trace log2 {}",
        d.rounds
    );
    // Every generated constant is a `Lit`: its value plus the readable numeric expression that
    // lands in the Solidity declaration (`10 * 16 * 16`, `1 << 4`, `32 * 12 + 12`, ...).
    let n = |v: usize| Lit::num(v as u128);
    let output_evals = Lit::pow2(output_log2 as u128);
    let num_outputs = n(EXPECTED_OUTPUT_TYPES.len()).mul(&n(2));
    assert_eq!(num_outputs.value as usize, d.num_outputs);
    let init_bytes = n(d.num_outputs).mul(&n(output_evals.value as usize)).mul(&n(16));
    let lsb_lines_bytes = n(d.num_outputs).mul(&n(32));
    let dim_reduce_layers = n(d.rounds).sub(&n(output_log2));
    let cap_lit = Lit::pow2(wc.cap_log2 as u128);
    let cap_bytes = n(cap).mul(&n(32));
    let pack = 1usize << pack_log2;
    let pack_lit = Lit::pow2(pack_log2 as u128);
    // ceil(num_memwit / pack), spelled `(num_memwit + pack - 1) >> pack_log2`
    let merged_mw = n(d.num_memwit)
        .add(&n(pack))
        .sub(&n(1))
        .shr(pack_log2 as u128);
    assert_eq!(merged_mw.value as usize, wc.merged_mw);

    // Transcript preimage layout: registers ‖ final_pc/ts ‖ top_bits ‖ setup_cap ‖ memory_cap.
    let final_pc_offset = n(super::NUM_REGISTERS).mul(&n(super::PREIMAGE_REGISTER_STRIDE));
    let top_bits_offset = final_pc_offset.add(&n(super::PREIMAGE_FINAL_PC_TS_BYTES));
    assert_eq!(
        top_bits_offset.value as usize,
        super::PREIMAGE_TOP_BITS_BYTE_OFFSET
    );
    let setup_cap_offset = top_bits_offset.add(&n(d.num_teardown_sets).mul(&n(4)));
    let memory_cap_offset = setup_cap_offset.add(&cap_bytes);
    let preimage_bytes = memory_cap_offset.add(&cap_bytes);
    // the register-file constants the template spells out must match the Rust definitions
    assert_eq!(
        read_const(GKR_TEMPLATE, "NUM_REGISTERS") as usize,
        super::NUM_REGISTERS
    );
    assert_eq!(
        read_const(GKR_TEMPLATE, "PREIMAGE_REGISTER_STRIDE") as usize,
        super::PREIMAGE_REGISTER_STRIDE
    );
    let mark_regs = read_const(GKR_TEMPLATE, "MARK_WORD_REGISTERS") as usize;
    assert_eq!(mark_regs * 4, 32, "a mark word must be exactly 32 bytes");
    for name in ["PUBLIC_INPUT_FIRST_REGISTER", "AUX_INPUT_FIRST_REGISTER"] {
        let first = read_const(GKR_TEMPLATE, name) as usize;
        assert!(
            first + mark_regs <= super::NUM_REGISTERS,
            "{name} + {mark_regs} exceeds the register file"
        );
    }

    // 1. GKR verifier: inline circuit.yul (replace the whole marker line, matching the awk
    //    splice the shell scripts used), then substitute circuit-derived + param constants.
    let (circuit_yul, stats) = emit_circuit_yul_with_stats(circuit);
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

    // 2. Heap layout: one bump allocator for both halves, starting right after the two
    //    spill-safe fixed slots (P_PTR, CIRCUIT_PTR) above the via_ir spill zone.
    let min_free = read_const(GKR_TEMPLATE, "MINIMUM_FREE_HEAP_PTR");
    assert_eq!(read_const(GKR_TEMPLATE, "P_PTR"), min_free);
    assert_eq!(read_const(GKR_TEMPLATE, "CIRCUIT_PTR"), min_free + 32);
    let mut heap = HeapAlloc::new(min_free + 64);
    let gkr_regions = gkr_heap_regions(
        &d,
        &stats,
        preimage_bytes.value as usize,
        &init_bytes,
        output_evals.value as usize,
        pack,
    );
    let mut assigned = BTreeSet::new();
    // The GKR regions are chained in the template by their sizes (`add(previous(), SIZE)`, see
    // the template's layout note for why not absolute literals): assign each region's padded
    // size and verify the template's accessor chain follows this allocation order exactly.
    let mut previous: Option<(&str, &str)> = None;
    for (name, accessor, size) in &gkr_regions {
        heap.region(name, size);
        gkr = set_const(
            &gkr,
            &format!("__TEMPLATE_GKR_{name}_BYTES"),
            size.expr(),
            &mut assigned,
        );
        let expected_body = match previous {
            None => "add(MINIMUM_FREE_HEAP_PTR, 64)".to_string(),
            Some((prev_name, prev_accessor)) => {
                format!("add({prev_accessor}(), __TEMPLATE_GKR_{prev_name}_BYTES)")
            }
        };
        let decl = format!("function {accessor}() -> ptr {{ ptr := {expected_body} }}");
        let squeeze = |s: &str| s.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(
            squeeze(&gkr).contains(&squeeze(&decl)),
            "gkr.sol heap chain out of sync with the allocator: expected `{decl}`"
        );
        previous = Some((name, accessor));
    }
    let _ = previous;

    for (name, value) in [
        ("__TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS", n(d.rounds)),
        ("__TEMPLATE_GKR_NUM_OUTPUTS", num_outputs.clone()),
        ("__TEMPLATE_GKR_OUTPUT_LOG2", n(output_log2)),
        ("__TEMPLATE_GKR_OUTPUT_EVALS", output_evals.clone()),
        ("__TEMPLATE_GKR_INIT_BYTES", init_bytes.clone()),
        ("__TEMPLATE_GKR_LSB_LINES_BYTES", lsb_lines_bytes),
        ("__TEMPLATE_GKR_DIM_REDUCE_LAYERS", dim_reduce_layers),
        ("__TEMPLATE_PREIMAGE_FINAL_PC_OFFSET", final_pc_offset),
        ("__TEMPLATE_PREIMAGE_TOP_BITS_OFFSET", top_bits_offset),
        ("__TEMPLATE_PREIMAGE_SETUP_CAP_OFFSET", setup_cap_offset),
        ("__TEMPLATE_PREIMAGE_MEMORY_CAP_OFFSET", memory_cap_offset),
        ("__TEMPLATE_GKR_INIT_PREIMAGE_BYTES", preimage_bytes.clone()),
        ("__TEMPLATE_EXTERNAL_POW_BITS", n(external_pow_bits as usize)),
        ("__TEMPLATE_WHIR_BATCH_POW_BITS", n(whir_batch_pow_bits as usize)),
        ("__TEMPLATE_EXPECTED_FINAL_PC", n(final_pc as usize)),
        ("__TEMPLATE_WHIR_NUM_MEMWIT", n(d.mem_width).add(&n(d.wit_width))),
        ("__TEMPLATE_WHIR_NUM_SETUP", n(d.num_setup)),
        ("__TEMPLATE_WHIR_MERGED_MW", merged_mw.clone()),
        ("__TEMPLATE_WHIR_PACK_LOG2", n(pack_log2)),
        ("__TEMPLATE_WHIR_PACK", pack_lit),
        ("__TEMPLATE_WHIR_BASE_Z_COORDS", n(d.rounds)),
        ("__TEMPLATE_WHIR_CAP", cap_lit.clone()),
    ] {
        gkr = set_const(&gkr, name, value.expr(), &mut assigned);
    }
    for (i, &tb) in inits_teardowns_top_bits.iter().enumerate() {
        gkr = set_const(
            &gkr,
            &format!("__TEMPLATE_INITS_TEARDOWNS_TOP_BITS_{i}"),
            tb,
            &mut assigned,
        );
    }

    // Boundary-layer LSB reorder for gkr_dr_final: the dim-reduce LSB lines are stored in
    // GKRAddress-offset order, but the g-accumulator wants OutputType-group (iteration) order so
    // grand-products land at logical slots 0,1,8,9. `SI[logical] = offset` = the artifact's
    // global_output_map value offsets flattened in iteration (BTreeMap<OutputType>) order.
    let gkr = gkr.replace(
        &format!("{SI_MARKER}\n"),
        &boundary_si_yul(circuit, d.num_outputs),
    );

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
    // the production source is just the verifier.
    let gkr = strip_from_contract(&gkr, "GKRVerifierTest");

    // 3. WHIR half: inject the per-round fold/query/PoW schedule generated from `wc`, then
    //    substitute every config-derived constant (schedule count, cap, RS-codeword domain
    //    generators, base-column geometry) and lay its memory regions out above the GKR heap.
    let whir_schedule_yul = wc.schedule_switch_yul();
    let mut whir = WHIR_TEMPLATE.replace(
        "            // __WHIR_SCHEDULE_SWITCH__",
        whir_schedule_yul.trim_end_matches('\n'),
    );
    assert!(
        !whir.contains("__WHIR_SCHEDULE_SWITCH__"),
        "whir.sol template missing the schedule marker"
    );
    // rfin = message_log2 - Σ folds, gcount = merged_mw + setup_merged + 1 — spelled out
    let folds_sum = wc.folds[1..]
        .iter()
        .fold(n(wc.folds[0]), |acc, &f| acc.add(&n(f)));
    let rfin = n(wc.message_log2).sub(&folds_sum);
    assert_eq!(rfin.value as usize, wc.rfin);
    let setup_merged = n(d.num_setup)
        .add(&n(pack))
        .sub(&n(1))
        .shr(pack_log2 as u128);
    assert_eq!(setup_merged.value as usize, wc.setup_merged);
    let gcount = merged_mw.add(&setup_merged).add(&n(1));
    assert_eq!(gcount.value as usize, wc.gcount);
    let nz = n(d.rounds).add(&n(pack_log2));
    assert_eq!(nz.value as usize, wc.nz);
    for (name, value) in [
        ("__TEMPLATE_WHIR_CAP", cap_lit.expr().to_string()),
        ("__TEMPLATE_WHIR_CAP_LOG2", wc.cap_log2.to_string()),
        ("__TEMPLATE_WHIR_NUM_ROUNDS", wc.num_rounds.to_string()),
        ("__TEMPLATE_WHIR_GEN", format!("0x{:032X}", wc.gen)),
        ("__TEMPLATE_WHIR_GEN_INV", format!("0x{:032X}", wc.gen_inv)),
        ("__TEMPLATE_WHIR_NZ", nz.expr().to_string()),
        ("__TEMPLATE_WHIR_GCOUNT", gcount.expr().to_string()),
        ("__TEMPLATE_WHIR_RFIN", rfin.expr().to_string()),
        ("__TEMPLATE_WHIR_MERGED_MW", merged_mw.expr().to_string()),
        ("__TEMPLATE_WHIR_SETUP_MERGED", setup_merged.expr().to_string()),
    ] {
        whir = set_const(&whir, name, value, &mut assigned);
    }
    let whir_regions = wc.memory_regions();
    // the template's compile-time layout guard compares the GKR chain end to the WHIR SEED region
    assert_eq!(whir_regions[0].0, "SEED_PTR");
    for (name, size) in &whir_regions {
        let addr = heap.region(name, size);
        whir = set_const(&whir, &format!("__TEMPLATE_WHIR_{name}"), addr, &mut assigned);
    }

    // 4. Splice the WHIR half into the GKR contract: one Solidity source, one transaction.
    let out = build_merged(&gkr, &whir, &heap);

    // 5. Every `__TEMPLATE_*` declaration in the merged source must have been assigned here.
    for line in out.lines() {
        if let Some(name) = const_decl_name(line) {
            if name.starts_with("__TEMPLATE_") {
                assert!(
                    assigned.contains(name),
                    "template constant {name} was never assigned by the generator"
                );
            }
        }
    }
    out
}

/// The GKR heap regions `(gkr.sol constant suffix, Yul accessor name, padded size as a
/// readable expression)` in allocation order (= the template's accessor chain order), every
/// size derived from the circuit / config and the emitted circuit.yul (see each entry).
fn gkr_heap_regions(
    d: &Derived,
    stats: &CircuitYulStats,
    preimage_bytes: usize,
    init_bytes: &Lit,
    output_evals: usize,
    pack: usize,
) -> Vec<(&'static str, &'static str, Lit)> {
    // Seed region: the seed word plus everything the template keeps right after it —
    //  * the transcript-absorb scratch at SEED+32/+64 (keccak256(SEED, 96) in
    //    transcript_4to1_dual, the 40-byte PoW absorb),
    //  * the preimage copy transcript_init keccaks in place (preimage_bytes),
    //  * circuit.yul's per-layer cache array at SEED+64 (GKR_CIRCUIT_CACHE_PTR, max_cache_slots).
    let seed_bytes = preimage_bytes
        .max(96)
        .max(64 + 32 * stats.max_cache_slots);
    // Absorb scratch: gkr_init's 32 + INIT_BYTES, the circuit layers' claims-batch absorbs, and
    // emit_gkr_mark's sub-buffers (packing coords at +0, merged claims at +128, whir_fold_pack's
    // PACK-slot chunk buffer at +384 — the fixed sub-offsets the template spells out).
    let pack_log2 = pack.trailing_zeros() as usize;
    assert!(
        pack_log2 * 32 <= 128,
        "emit_gkr_mark keeps the {pack_log2} packing coords in the 128-byte slot before the merged claims"
    );
    assert!(
        128 + (d.merged_mw + 1) * 32 <= 384,
        "emit_gkr_mark keeps the {} merged claims in [+128, +384) of the absorb scratch",
        d.merged_mw + 1
    );
    let abs_bytes = if 32 + init_bytes.value as usize >= stats.max_absorb_bytes.max(384 + pack * 32)
    {
        Lit::num(32).add(init_bytes) // the seed word + gkr_init's output-evals absorb
    } else {
        words_for(stats.max_absorb_bytes.max(384 + pack * 32))
    };
    let w = |n: usize| Lit::words(n as u128);
    vec![
        ("MEMORY_CHALLS", "MEMORY_CHALLS_PTR", w(7)), // 6 perm-linearization challenges + additive
        ("LOGUP_CHALLS", "LOGUP_CHALLS_PTR", w(2)),   // alpha, additive
        ("POINT", "POINT_PTR", w(d.rounds)), // the claim point grows to trace_log2 coords
        ("INIT_GAS", "GKR_INIT_GAS_PTR", Lit::num(32)),
        ("MAIN_GAS", "GKR_MAIN_GAS_PTR", Lit::num(32)),
        ("SEED", "SEED_PTR", words_for(seed_bytes)),
        ("BATCHING", "GKR_BATCHING_PTR", Lit::num(32)),
        ("CLAIMS", "GKR_CLAIMS_PTR", w(d.num_outputs)),
        // eq[OUTPUT_EVALS] for the entry claims; reused as SI[NUM_OUTPUTS] by gkr_dr_final
        ("EQ", "GKR_EQ_PTR", w(output_evals.max(d.num_outputs))),
        ("ABS", "GKR_ABS_PTR", abs_bytes),
        ("PERM_PROD", "GKR_PERM_PROD_PTR", w(4)),
        ("CIRCUIT_CLAIMS", "GKR_CIRCUIT_CLAIMS_PTR", w(stats.max_claims_slots)),
        ("GATEVAL", "GKR_GATEVAL_PTR", w(stats.gateval_slots)),
        ("QTABLE", "GKR_QTABLE_PTR", words_for(stats.qtable_bytes)),
    ]
}

// ── Splicing the WHIR half into the GKR contract ────────────────────────────────────────────
//
// whir.sol is a template FRAGMENT: its Yul (the helper functions + `whir_verify(cd_start)`) is
// inlined into the GKR template's single `assembly ("memory-safe")` block, where the GKR half's
// `emit_gkr_mark` writes the GKR→WHIR handoff state straight into the WHIR memory regions and
// the fallback tail calls `whir_verify`. What the splice has to respect:
//  * one Yul block → no name clashes: whir.sol's `__TEMPLATE_WHIR_*` constants are unique by
//    construction (the GKR template declares a few of the same names for the handoff — those
//    are SHARED: declared once, with the generator-assigned values checked equal); every other
//    whir.sol constant is prefixed `W_`. The Yul function names were checked disjoint (whir:
//    batch_oracle, do_*, draw*, fold_*, ...).
//  * memory-safe assembly: via_ir spills into [0x80, MINIMUM_FREE_HEAP_PTR); the GKR heap and
//    then every WHIR region are laid out above it by the same bump allocator, so nothing
//    overlaps; the WHIR half never touches 0x40/0x60, and the end-of-fallback spill guard is
//    re-checked after it.

/// `__TEMPLATE_WHIR_*` names the GKR template references (handoff) — must come from whir.sol.
const GKR_REQUIRED_WHIR_CONSTS: &[&str] = &[
    "__TEMPLATE_WHIR_SEED_PTR",
    "__TEMPLATE_WHIR_HANDOFF_BATCHING_PTR",
    "__TEMPLATE_WHIR_REG_CLAIM",
    "__TEMPLATE_WHIR_Z_PTR",
    "__TEMPLATE_WHIR_BCAP0_PTR",
    "__TEMPLATE_WHIR_BCAP1_PTR",
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

/// The literal RHS text of a constant declaration line.
fn decl_rhs(line: &str) -> &str {
    let eq = line.find('=').unwrap();
    let semi = eq + line[eq..].find(';').unwrap();
    line[eq + 1..semi].trim()
}

/// Splice the (substituted) whir.sol fragment into the (substituted) GKR source, appending the
/// generated heap map as documentation.
fn build_merged(gkr: &str, whir: &str, heap: &HeapAlloc) -> String {
    let lines: Vec<&str> = whir.lines().collect();

    // 1. WHIR constants: the block `HALF` .. `__TEMPLATE_WHIR_FEVAL_PTR` (P / MASK precede HALF;
    //    shared with GKR).
    let cs = line_idx(&lines, "uint256 constant HALF", "constants start");
    let ce = line_idx(
        &lines,
        "uint256 constant __TEMPLATE_WHIR_FEVAL_PTR",
        "constants end",
    );
    let mut consts = String::new();
    let mut prefixed: Vec<String> = Vec::new();
    for &line in &lines[cs..=ce] {
        let Some(name) = const_decl_name(line) else {
            consts.push_str(line);
            consts.push('\n');
            continue;
        };
        if name.starts_with("__TEMPLATE_WHIR_") {
            // shared with the GKR template? then it is declared there, with the same value
            if let Some(gline) = gkr.lines().find(|l| const_decl_name(l) == Some(name)) {
                assert_eq!(
                    decl_rhs(gline),
                    decl_rhs(line),
                    "shared constant {name} differs between the GKR and WHIR templates"
                );
                continue;
            }
            consts.push_str(line);
            consts.push('\n');
        } else {
            consts.push_str(line);
            consts.push('\n');
            prefixed.push(name.to_string());
        }
    }

    // 2. the Yul: everything between the assembly open and the end marker (helper functions +
    //    `whir_verify(cd_start)`, both already in the shape the merged contract needs).
    let asm_open = line_idx(&lines, "        assembly {", "assembly block");
    let yul_end = line_idx(&lines, "// __WHIR_YUL_END__", "Yul end marker");
    assert!(
        asm_open < yul_end,
        "whir.sol template: Yul end marker precedes the assembly block"
    );
    let mut whir_yul = lines[asm_open + 1..yul_end].join("\n");
    whir_yul.push('\n');

    // 3. prefix the non-template WHIR constants so nothing collides with the GKR template's names
    for n in &prefixed {
        let to = format!("W_{n}");
        assert!(
            !gkr.contains(&format!("constant {to} ")),
            "GKR template already declares {to}"
        );
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
        "__TEMPLATE_VERIFIED_TOPIC",
        "W_SEED_PTR",
        "whir_fold16",
        // a declaration still holding the templates' placeholder (would not compile anyway)
        "= \"{unassigned}\"",
    ] {
        assert!(
            !out.contains(leftover),
            "merged source still contains `{leftover}`"
        );
    }
    for req in GKR_REQUIRED_WHIR_CONSTS {
        assert!(
            out.contains(&format!("constant {req} ")),
            "the GKR template references {req} but whir.sol did not provide it"
        );
    }

    // 5. document the generated heap map at the end of the source
    let mut out = out;
    out.push_str("\n// Generated heap map (byte offsets; every region sized from the circuit / prover config):\n");
    for (name, start, size) in &heap.regions {
        out.push_str(&format!(
            "//   {start:>6} .. {:>6}  {name} ({} = {} B)\n",
            start + size.value,
            size.expr(),
            size.value
        ));
    }
    out.push_str(&format!("//   heap end: {}\n", heap.next));
    out
}
