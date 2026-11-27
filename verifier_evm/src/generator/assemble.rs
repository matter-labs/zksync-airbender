//! Assemble the merged verifier Solidity from the circuit artifact + caller-supplied params.
//!
//! The GKR verifier is the hand-written `gkr.sol` template with the circuit-specific
//! `circuit.yul` inlined at `// __INLINE_CIRCUIT_YUL__` and the WHIR fragment (`whir.sol`)
//! spliced in; EVERY `__TEMPLATE_*` constant of both templates is assigned here. The rule the
//! templates follow: anything the compiled circuit or the prover config is the source of truth
//! for — widths, output counts, cap size, preimage offsets, the whole heap map — is referenced
//! by its `__TEMPLATE_*` NAME in the Solidity/Yul and gets its literal value from this file
//! (inline assembly can only consume literal constants, so the literal lives in the
//! declaration alone). The program's terminal PC and inits/teardowns top bits are
//! deployment parameters. PoW difficulties are derived from the circuit and prover config,
//! with the L1 wrap's external-challenge floor.
//!
//! The WHIR *proving-config* (fold/query/PoW schedule, base rate, merkle cap) is not encoded in
//! the circuit artifact; it is supplied by the caller as the same `ProverConfig` the prover used,
//! including its packing factor. This config drives both halves of the merged verifier — see
//! [`WhirGenConfig`].

use super::whir::WhirGenConfig;
use super::{
    calldata_decoder, emit_circuit_yul_with_stats, CircuitYulStats, Lit, WrapContracts,
    MAX_NONCE_POW_BITS,
};
use crate::encoding::{FormatParams, Geometry};
use cs::definitions::{GKRAddress, OutputType};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::gkr::prover_config::{pow_bits, ProverConfig};
use prover::merkle_trees::keccak256_hash_leafs::KECCAK256_MERKLE_DIGEST_BYTES as DIGEST_BYTES;
use prover::transcript::Keccak256Transcript;
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
            if i == 0 {
                "            ptr := sumcheck_circuit_layer0(ptr, alpha)\n".to_string()
            } else {
                format!("            ptr, alpha := sumcheck_circuit_layer{i}(ptr, alpha)\n")
            }
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
    // gkr_dr_final fills its sorted-index array (`SI` in gkr.sol) with the identity first: emit
    // only the entries that differ
    offsets
        .iter()
        .enumerate()
        .filter(|&(i, off)| i != *off)
        .map(|(i, off)| format!("                mstore(add(SI, {}), {off}) // logical output {i} maps to address-sorted LSB slot {off}\n", i * 32))
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

/// Circuit-derived layout values used to substitute the gkr.sol constants.
struct Derived {
    rounds: usize,
    mem_width: usize,
    wit_width: usize,
    num_memwit: usize,
    num_setup: usize,
    merged_mw: usize,
    setup_merged: usize,
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
            assert_eq!(
                addrs.len(),
                2,
                "output type {ty:?} must have exactly 2 lines"
            );
        }
        let num_outputs = circuit.global_output_map.values().map(Vec::len).sum();
        Self {
            rounds,
            mem_width: circuit.memory_layout.total_width,
            wit_width: circuit.witness_layout.total_width,
            num_memwit,
            num_setup: circuit.generic_lookup_tables_width,
            merged_mw: num_memwit.div_ceil(1 << pack_log2),
            setup_merged: circuit.generic_lookup_tables_width.div_ceil(1 << pack_log2),
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
    regions: Vec<HeapRegion>,
}

struct HeapRegion {
    name: String,
    accessor: String,
    start: u128,
    size: Lit,
    purpose: &'static str,
}

impl HeapAlloc {
    fn new(base: u128) -> Self {
        Self {
            next: base,
            regions: Vec::new(),
        }
    }
    /// Append a region; `size` is the region's padded size (a positive multiple of 32).
    fn region(&mut self, name: &str, accessor: &str, size: &Lit, purpose: &'static str) -> u128 {
        assert!(
            size.value > 0 && size.value.is_multiple_of(32),
            "heap region {name}: size {} = {} must be a positive multiple of 32",
            size.expr(),
            size.value
        );
        let start = self.next;
        self.next += size.value;
        self.regions.push(HeapRegion {
            name: name.to_string(),
            accessor: accessor.to_string(),
            start,
            size: size.clone(),
            purpose,
        });
        start
    }
}

/// `32 * ceil(bytes / 32)` — a byte count rounded up to whole 32-byte words.
fn words_for(bytes: usize) -> Lit {
    Lit::words((bytes as u128).div_ceil(32))
}

fn hex_bytes(data: &[u8]) -> String {
    data.iter().map(|b| format!("{b:02x}")).collect()
}

/// Append the unchanged setup payload to the runtime generated for one registry.
/// Reading from the code tail keeps Solidity's metadata trailer outside the setup layout.
fn deployment_sol(runtime: &str, data: &[u8]) -> String {
    format!(
        "{runtime}\ncontract GkrWhirVerifier is GkrWhirVerifierCode {{
    constructor() {{
        // Runtime layout: Solidity code (including metadata) | setup data.
        bytes memory code = bytes.concat(type(GkrWhirVerifierCode).runtimeCode, hex\"{hex}\");
        assembly (\"memory-safe\") {{
            return(add(code, 32), mload(code))
        }}
    }}
}}
",
        hex = hex_bytes(data),
    )
}

/// The GKR decoder and setup frontier (nodes, level and skipped levels).
struct WrapRender {
    decoder: calldata_decoder::GkrDecoder,
    frontier: (Vec<u8>, usize, usize),
}

/// The single-transaction wrap verifier: every proof byte is read from the compressed calldata,
/// the final PC and `setup_cap` are deployment constants. The setup cap and the GKR term table
/// are appended to the runtime code by the no-argument constructor. The nodes at
/// `params.setup_frontier_level` (physical order) precede the cap and table after a STOP byte.
/// `registry_address` is compiled into the runtime, like the final PC and setup. Regenerate
/// the verifier if it changes. It must be nonzero; checking deployed registry code is the
/// deployer's responsibility, since the registry may be deployed after source generation.
#[allow(clippy::too_many_arguments)]
pub fn generate_wrap_verifier(
    circuit: &GKRCircuitArtifact<Proth120>,
    prover_config: &ProverConfig,
    params: &FormatParams,
    final_pc: u32,
    inits_teardowns_top_bits: &[u32],
    setup_cap: &[[u32; 8]],
    setup_frontier: &[[u32; 8]],
    registry_address: [u8; 20],
) -> WrapContracts {
    assert_ne!(registry_address, [0; 20], "registry is zero");
    let params = &Geometry::from_config(prover_config, params);
    assert_eq!(setup_cap.len(), params.cap(), "setup cap size");
    let frontier = {
        let nodes = setup_frontier;
        assert_eq!(
            nodes.len(),
            1 << params.setup_frontier_level,
            "setup frontier size"
        );
        assert_eq!(
            crate::encoding::merkle_reduce(nodes, params.setup_frontier_skip()),
            setup_cap,
            "the setup frontier does not reduce to the setup cap"
        );
        nodes
            .iter()
            .flat_map(crate::encoding::digest_wire)
            .collect::<Vec<u8>>()
    };
    let decoder = calldata_decoder::gkr_decoder(
        circuit,
        params,
        final_pc,
        setup_cap,
        inits_teardowns_top_bits,
    );
    let wrap_render = WrapRender {
        decoder,
        frontier: (
            frontier,
            params.setup_frontier_level,
            params.setup_frontier_skip(),
        ),
    };
    let (verifier_sol, data, memory_layout) = render(
        circuit,
        prover_config,
        inits_teardowns_top_bits,
        &wrap_render,
        registry_address,
    );
    WrapContracts {
        verifier_sol: deployment_sol(&verifier_sol, &data),
        memory_layout,
    }
}

fn render(
    circuit: &GKRCircuitArtifact<Proth120>,
    prover_config: &ProverConfig,
    inits_teardowns_top_bits: &[u32],
    wrap: &WrapRender,
    registry_address: [u8; 20],
) -> (String, Vec<u8>, String) {
    // Every proving-geometry parameter comes from the prover config: the packing
    // factor, the message size and the WHIR batching PoW difficulty (which the
    // prover derives from the config + the circuit exactly like this).
    let pack_log2 = prover_config.pack_log2();
    assert!(pack_log2 > 0, "pack_log2 must be positive");
    assert!(
        prover_config.merged_memory_and_witness(),
        "the EVM verifier serves the single merged memory+witness commitment"
    );
    // The schedule owns the base rate and leaf width; the config accessors
    // read that same geometry, so no independent consistency pins are needed.
    let d = Derived::from(circuit, pack_log2);
    assert_eq!(
        prover_config.trace_len_log2, d.rounds,
        "prover config trace_len_log2 {} != circuit trace log2 {}",
        prover_config.trace_len_log2, d.rounds
    );
    let whir_batch_pow_bits = prover_config
        .base_round()
        .batching_pow_bits::<Proth120, Proth120>(
            prover_config.security_level.security_bits(),
            prover_config.whir_message_size_log2(),
            pow_bits::committed_base_oracle_columns(circuit, pack_log2, true),
        );
    let lookup_pow_bits =
        prover_config.lookup_challenges_pow_bits::<_, _, Keccak256Transcript>(circuit);
    let external_pow_bits = lookup_pow_bits
        .max(prover::gkr::prover_config::example_configs::l1_wrap::EXTERNAL_CHALLENGES_POW_BITS);
    for (gate, bits) in [
        ("external challenges", external_pow_bits),
        ("WHIR batching", whir_batch_pow_bits),
    ] {
        // Limit claimed difficulty to the width of the calldata nonce.
        assert!(
            bits <= MAX_NONCE_POW_BITS,
            "{gate} PoW {bits} exceeds the {MAX_NONCE_POW_BITS}-bit calldata nonce width"
        );
    }
    // WHIR config derived from the same source the prover used, plus the artifact's widths.
    let wc = WhirGenConfig::derive(prover_config, d.num_memwit, d.num_setup);
    // GKR↔WHIR consistency: the shared parameters must agree between the two halves.
    assert_eq!(
        wc.merged_mw, d.merged_mw,
        "GKR/WHIR merged mem+wit width disagree ({} vs {})",
        wc.merged_mw, d.merged_mw
    );
    assert_eq!(
        wc.setup_merged, d.setup_merged,
        "GKR/WHIR merged setup width disagree ({} vs {})",
        wc.setup_merged, d.setup_merged
    );
    assert_eq!(
        prover_config.cap_size, prover_config.whir_schedule.cap_size,
        "the templates use one merkle cap size for the base oracles and the WHIR oracles"
    );

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
    assert!(
        inits_teardowns_top_bits
            .windows(2)
            .all(|pair| pair[0] < pair[1]),
        "inits/teardowns top bits must be strictly increasing"
    );

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
    let init_bytes = n(d.num_outputs)
        .mul(&n(output_evals.value as usize))
        .mul(&n(16));
    let lsb_lines_bytes = n(d.num_outputs).mul(&n(32));
    let dim_reduce_layers = n(d.rounds).sub(&n(output_log2));
    let cap_lit = Lit::pow2(wc.cap_log2 as u128);
    let pack = 1usize << pack_log2;
    let pack_lit = Lit::pow2(pack_log2 as u128);
    // ceil(num_memwit / pack), spelled `(num_memwit + pack - 1) >> pack_log2`
    let merged_mw = n(d.num_memwit)
        .add(&n(pack))
        .sub(&n(1))
        .shr(pack_log2 as u128);
    assert_eq!(merged_mw.value as usize, wc.merged_mw);
    let setup_merged = n(d.num_setup)
        .add(&n(pack))
        .sub(&n(1))
        .shr(pack_log2 as u128);
    assert_eq!(setup_merged.value as usize, wc.setup_merged);
    // emit_gkr_mark's ABS scratch: packing coords, then the merged claims, then the fold buffer
    let handoff_merged_offset = Lit::words(pack_log2 as u128);
    let handoff_fold_offset = Lit::words((pack_log2 + d.merged_mw + d.setup_merged) as u128);

    // Transcript preimage layout: registers ‖ final_pc/ts ‖ top_bits ‖ setup_cap ‖ memory_cap.
    let preimage = &wrap.decoder.preimage;
    assert_eq!(
        preimage.top_bits.value as usize,
        super::PREIMAGE_TOP_BITS_BYTE_OFFSET
    );
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

    // 2. Heap layout: one bump allocator for both halves, starting right after the three
    //    spill-safe fixed slots (P_PTR, CIRCUIT_PTR, SETUP_CODE_OFFSET_PTR) above the via_ir spill zone.
    let min_free = read_const(GKR_TEMPLATE, "MINIMUM_FREE_HEAP_PTR");
    assert_eq!(read_const(GKR_TEMPLATE, "P_PTR"), min_free);
    assert_eq!(read_const(GKR_TEMPLATE, "CIRCUIT_PTR"), min_free + 32);
    assert_eq!(
        read_const(GKR_TEMPLATE, "SETUP_CODE_OFFSET_PTR"),
        min_free + 64
    );
    let mut heap = HeapAlloc::new(min_free + 96);
    let seed = SeedLayout::from(&stats);
    let gkr_regions = gkr_heap_regions(
        &d,
        &stats,
        &init_bytes,
        output_evals.value as usize,
        pack,
        wrap.decoder.image_bytes,
    );
    let mut assigned = BTreeSet::new();
    let marker = "    // __GKR_LAYER_CLAIMS_CONSTANTS__";
    assert_eq!(gkr.matches(marker).count(), 1);
    let declarations: String = stats.layer_claim_counts.iter().enumerate().map(|(i, _)| {
        format!("    uint256 constant __TEMPLATE_GKR_LAYER_{i}_CLAIMS = \"{{unassigned}}\"; // previous-layer output claims batched by sccl{i}\n")
    }).collect();
    gkr = gkr.replace(marker, declarations.trim_end());
    for (i, count) in stats.layer_claim_counts.iter().enumerate() {
        gkr = set_const(
            &gkr,
            &format!("__TEMPLATE_GKR_LAYER_{i}_CLAIMS"),
            count,
            &mut assigned,
        );
    }
    gkr = set_const(
        &gkr,
        "__TEMPLATE_REGISTRY",
        format!("address(0x00{})", hex_bytes(&registry_address)),
        &mut assigned,
    );
    gkr = set_const(
        &gkr,
        "__TEMPLATE_GKR_CACHE_OFFSET",
        seed.cache_offset,
        &mut assigned,
    );
    // The GKR regions are chained in the template by their sizes (`add(previous(), SIZE)`, see
    // the template's layout note for why not absolute literals): assign each region's padded
    // size and verify the template's accessor chain follows this allocation order exactly.
    // The last region's size only advances the allocator: no accessor follows it.
    let mut previous: Option<(&str, &str)> = None;
    for (idx, (name, accessor, size, purpose)) in gkr_regions.iter().enumerate() {
        heap.region(name, accessor, size, purpose);
        if idx + 1 < gkr_regions.len() {
            gkr = set_const(
                &gkr,
                &format!("__TEMPLATE_GKR_{name}_BYTES"),
                size.expr(),
                &mut assigned,
            );
        }
        let expected_body = match previous {
            None => "add(MINIMUM_FREE_HEAP_PTR, 96)".to_string(),
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
    // Tie the exact POINT allocation to each template write loop, including the last
    // dimension-reduction shift (which writes index fs, not fs - 1).
    let last_shift_index = output_log2 + dim_reduce_layers.value as usize - 1;
    let max_point_index = last_shift_index.max(output_log2 - 1).max(d.rounds - 1);
    let point = heap.regions.iter().find(|r| r.name == "POINT").unwrap();
    assert_eq!(point.size.value, 32 * (max_point_index + 1) as u128);
    for write_bound in [
        "lt(i, __TEMPLATE_GKR_OUTPUT_LOG2)",
        "lt(i, total_rounds)",
        "for { let k := 0 } lt(k, __TEMPLATE_GKR_DIM_REDUCE_LAYERS) { k := add(k, 1) }",
        "let fs := add(__TEMPLATE_GKR_OUTPUT_LOG2, k)",
        "ptr, claim := sumcheck_rounds(ptr, claim, fs)",
        "for { let sh := fs } gt(sh, 0) { sh := sub(sh, 1) }",
        "mstore(add(POINT_PTR(), mul(sh, 32)), mload(add(POINT_PTR(), mul(sub(sh, 1), 32))))",
    ] {
        assert!(
            GKR_TEMPLATE.contains(write_bound),
            "POINT write-bound template changed: {write_bound}"
        );
    }

    for (name, value) in [
        ("__TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS", n(d.rounds)),
        ("__TEMPLATE_GKR_NUM_OUTPUTS", num_outputs.clone()),
        ("__TEMPLATE_GKR_OUTPUT_LOG2", n(output_log2)),
        ("__TEMPLATE_GKR_OUTPUT_EVALS", output_evals.clone()),
        ("__TEMPLATE_GKR_INIT_BYTES", init_bytes.clone()),
        ("__TEMPLATE_GKR_LSB_LINES_BYTES", lsb_lines_bytes),
        ("__TEMPLATE_GKR_DIM_REDUCE_LAYERS", dim_reduce_layers),
        (
            "__TEMPLATE_EXTERNAL_POW_BITS",
            n(external_pow_bits as usize),
        ),
        (
            "__TEMPLATE_WHIR_BATCH_POW_BITS",
            n(whir_batch_pow_bits as usize),
        ),
        (
            "__TEMPLATE_WHIR_NUM_MEMWIT",
            n(d.mem_width).add(&n(d.wit_width)),
        ),
        ("__TEMPLATE_WHIR_NUM_SETUP", n(d.num_setup)),
        ("__TEMPLATE_WHIR_MERGED_MW", merged_mw.clone()),
        ("__TEMPLATE_WHIR_SETUP_MERGED", setup_merged.clone()),
        (
            "__TEMPLATE_GKR_HANDOFF_MERGED_OFFSET",
            handoff_merged_offset,
        ),
        ("__TEMPLATE_GKR_HANDOFF_FOLD_OFFSET", handoff_fold_offset),
        ("__TEMPLATE_WHIR_PACK_LOG2", n(pack_log2)),
        ("__TEMPLATE_WHIR_PACK", pack_lit),
        ("__TEMPLATE_WHIR_BASE_Z_COORDS", n(d.rounds)),
        ("__TEMPLATE_WHIR_CAP", cap_lit.clone()),
    ] {
        gkr = set_const(&gkr, name, value.expr(), &mut assigned);
    }
    // Assign logical column indices in the same flattened OutputType order as boundary_si_yul.
    // Derived::from checks the grouping/width assumptions used by the template's lookup loops.
    let mut output_column = 0;
    for (output_type, outputs) in &circuit.global_output_map {
        let names = match output_type {
            OutputType::PermutationProduct => [
                "__TEMPLATE_GKR_OUTPUT_PERM_READ",
                "__TEMPLATE_GKR_OUTPUT_PERM_WRITE",
            ],
            OutputType::Lookup16Bits => [
                "__TEMPLATE_GKR_OUTPUT_LOOKUP16_NUM",
                "__TEMPLATE_GKR_OUTPUT_LOOKUP16_DEN",
            ],
            OutputType::LookupTimestamps => [
                "__TEMPLATE_GKR_OUTPUT_LOOKUP_TS_NUM",
                "__TEMPLATE_GKR_OUTPUT_LOOKUP_TS_DEN",
            ],
            OutputType::GenericLookup => [
                "__TEMPLATE_GKR_OUTPUT_GENERIC_LOOKUP_NUM",
                "__TEMPLATE_GKR_OUTPUT_GENERIC_LOOKUP_DEN",
            ],
            OutputType::InitsAndTeardownsProduct => [
                "__TEMPLATE_GKR_OUTPUT_TEARDOWN",
                "__TEMPLATE_GKR_OUTPUT_INIT",
            ],
        };
        assert_eq!(names.len(), outputs.len());
        for name in names {
            gkr = set_const(&gkr, name, output_column, &mut assigned);
            output_column += 1;
        }
    }
    assert_eq!(
        output_column, num_outputs.value as usize,
        "named GKR output columns must cover every output poly"
    );
    for (name, value) in preimage.constants() {
        gkr = set_const(&gkr, name, value.expr(), &mut assigned);
    }
    // The generated template length and the decoder's image prefix share one layout.
    assert!(gkr.lines().any(|line| const_decl_name(line)
        == Some("__TEMPLATE_GKR_INIT_PREIMAGE_BYTES")
        && decl_rhs(line) == preimage.total.expr()));
    for (i, &tb) in inits_teardowns_top_bits.iter().enumerate() {
        gkr = set_const(
            &gkr,
            &format!("__TEMPLATE_INITS_TEARDOWNS_TOP_BITS_{i}"),
            tb,
            &mut assigned,
        );
    }
    gkr = set_const(
        &gkr,
        "__TEMPLATE_FACTORED_ROUND_SLOT_BYTES",
        calldata_decoder::FACTORED_ROUND_SLOT_BYTES,
        &mut assigned,
    );

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

    // The GKR half reads the decoded GKR image (every calldata access rewritten; the absolute
    // preimage readers add IMAGE_PTR() in the template), the decoder is the only GKR calldata
    // reader, and the WHIR stream starts after the calldata's GKR section.
    let gkr = {
        let f = wrap;
        let gkr = calldata_decoder::calldata_reads_to_image_reads(&gkr);
        let marker = "        // __CALLDATA_DECODER__\n";
        assert_eq!(
            gkr.matches(marker).count(),
            1,
            "gkr.sol misses the calldata decoder marker"
        );
        assert_eq!(gkr.matches("__WHIR_START__").count(), 1);
        gkr.replace(marker, &f.decoder.yul)
            .replace("__WHIR_START__", &f.decoder.calldata_bytes.to_string())
    };

    // 3. WHIR half: inject the per-round fold/query/PoW schedule generated from `wc`, then
    //    substitute every config-derived constant (schedule count, cap, RS-codeword domain
    //    generators, base-column geometry) and lay its memory regions out above the GKR heap.
    let whir_schedule_yul = wc.schedule_switch_yul();
    let mut whir = WHIR_TEMPLATE.replace(
        "            // __WHIR_SCHEDULE_SWITCH__",
        whir_schedule_yul.trim_end_matches('\n'),
    );
    let (roots, query_root, final_root) = if wc.variable_domains() {
        (
            wc.oracle_roots_yul(),
            "oracle_root(r)",
            format!("0x{:032X}", wc.oracle_root(wc.num_rounds - 1)),
        )
    } else {
        (
            String::new(),
            "__TEMPLATE_WHIR_BASE_DOMAIN_ROOT",
            "__TEMPLATE_WHIR_BASE_DOMAIN_ROOT".into(),
        )
    };
    for (marker, value) in [
        ("        // __ORACLE_ROOTS__\n", roots.as_str()),
        (
            "/*__QUERY_ORACLE_ROOT__*/__TEMPLATE_WHIR_BASE_DOMAIN_ROOT",
            query_root,
        ),
        (
            "/*__FINAL_ORACLE_ROOT__*/__TEMPLATE_WHIR_BASE_DOMAIN_ROOT",
            final_root.as_str(),
        ),
    ] {
        assert_eq!(
            whir.matches(marker).count(),
            1,
            "WHIR template marker {marker}"
        );
        whir = whir.replace(marker, value);
    }
    let setup_data = {
        let f = wrap;
        assert_eq!(whir.matches("        // __FINAL_HORNER__").count(), 1);
        assert_eq!(whir.matches("__HORNER_NAME__").count(), 2);
        whir = whir
            .replace(
                "        // __FINAL_HORNER__",
                wc.final_horner_yul().trim_end_matches('\n'),
            )
            .replace("__HORNER_NAME__", &format!("horner_{}", 1usize << wc.rfin));
        whir = set_const(
            &whir,
            "__TEMPLATE_DIGEST_BYTES",
            DIGEST_BYTES,
            &mut assigned,
        );
        let nodes = &f.frontier.0[..];
        let stop = [0u8];
        let frontier_offset = stop.len();
        let cap_offset = frontier_offset + nodes.len();
        let qtable_offset = cap_offset + f.decoder.setup_cap_image.len();
        let data = [&stop[..], nodes, &f.decoder.setup_cap_image, &stats.qtable].concat();
        for (name, value) in [
            ("__TEMPLATE_SETUP_DATA_BYTES", data.len().to_string()),
            (
                "__TEMPLATE_DATA_FRONTIER_OFFSET",
                frontier_offset.to_string(),
            ),
            (
                "__TEMPLATE_DATA_CAP_BYTES",
                f.decoder.setup_cap_image.len().to_string(),
            ),
            (
                "__TEMPLATE_DATA_QTABLE_BYTES",
                stats.qtable.len().to_string(),
            ),
            ("__TEMPLATE_DATA_CAP_OFFSET", cap_offset.to_string()),
            ("__TEMPLATE_DATA_QTABLE_OFFSET", qtable_offset.to_string()),
        ] {
            whir = set_const(&whir, name, value, &mut assigned);
        }
        {
            let (_, level, skip) = &f.frontier;
            for (name, value) in [
                ("__TEMPLATE_FRONTIER_LEVEL", level.to_string()),
                ("__TEMPLATE_FRONTIER_SKIP", skip.to_string()),
            ] {
                whir = set_const(&whir, name, value, &mut assigned);
            }
        }
        data
    };
    whir = set_const(
        &whir,
        "__TEMPLATE_DIGEST_MASK",
        format!(
            "0x{}{}",
            "ff".repeat(DIGEST_BYTES),
            "00".repeat(32 - DIGEST_BYTES)
        ),
        &mut assigned,
    );
    assert!(
        !whir.contains("__WHIR_SCHEDULE_SWITCH__"),
        "whir.sol template missing the schedule marker"
    );
    // rfin = message_log2 - Σ folds spelled out; gcount = merged_mw + setup_merged, checked
    let folds_sum = wc.folds[1..]
        .iter()
        .fold(n(wc.folds[0]), |acc, &f| acc.add(&n(f)));
    let rfin = n(wc.message_log2).sub(&folds_sum);
    assert_eq!(rfin.value as usize, wc.rfin);
    let gcount = merged_mw.add(&setup_merged);
    assert_eq!(gcount.value as usize, wc.gcount);
    let nz = n(d.rounds).add(&n(pack_log2));
    assert_eq!(nz.value as usize, wc.nz);
    for (name, value) in [
        ("__TEMPLATE_WHIR_CAP", cap_lit.expr().to_string()),
        ("__TEMPLATE_WHIR_CAP_LOG2", wc.cap_log2.to_string()),
        ("__TEMPLATE_WHIR_NUM_ROUNDS", wc.num_rounds.to_string()),
        (
            "__TEMPLATE_WHIR_BASE_DOMAIN_ROOT",
            format!("0x{:032X}", wc.base_domain_root),
        ),
        (
            "__TEMPLATE_WHIR_BASE_DOMAIN_ROOT_INV",
            format!("0x{:032X}", wc.base_domain_root_inv),
        ),
        ("__TEMPLATE_WHIR_RFIN", rfin.expr().to_string()),
        ("__TEMPLATE_WHIR_MERGED_MW", merged_mw.expr().to_string()),
        (
            "__TEMPLATE_WHIR_SETUP_MERGED",
            setup_merged.expr().to_string(),
        ),
    ] {
        whir = set_const(&whir, name, value, &mut assigned);
    }
    let whir_regions = wc.memory_regions();
    for (name, size, purpose) in &whir_regions {
        let accessor = format!("__TEMPLATE_WHIR_{name}");
        let addr = heap.region(&format!("WHIR_{name}"), &accessor, size, purpose);
        whir = set_const(
            &whir,
            &format!("__TEMPLATE_WHIR_{name}"),
            addr,
            &mut assigned,
        );
    }

    // 4. Splice the WHIR half into the GKR contract: one Solidity source, one transaction.
    let out = build_merged(&gkr, &whir, &heap);
    // Every sumcheck_rounds call writes POINT[0..total_rounds): only the dimension-reduction
    // `fs` (at most rounds - 1) and the circuit layers' CIRCUIT_LAYER_ROUNDS (= rounds) are
    // within the POINT allocation checked above.
    for call in out
        .match_indices("sumcheck_rounds(")
        .map(|(i, _)| &out[i..])
    {
        let args = &call["sumcheck_rounds(".len()..call.find(')').unwrap()];
        assert!(
            matches!(
                args,
                "ptr, claim, total_rounds"
                    | "ptr, claim, fs"
                    | "ptr, claim, __TEMPLATE_GKR_CIRCUIT_LAYER_ROUNDS"
            ),
            "sumcheck_rounds call with an unchecked round count: `{args}`"
        );
    }

    // Every template use must have an assigned value, including names emitted by circuit.yul.
    for line in out.lines() {
        let trimmed = line.trim();
        assert!(
            !trimmed.starts_with("// #if") && trimmed != "// #else" && trimmed != "// #endif",
            "unresolved template directive: {trimmed}"
        );
        let code = line.split_once("//").map_or(line, |(code, _)| code);
        for token in code.split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_') {
            if token.starts_with("__TEMPLATE_") {
                assert!(
                    assigned.contains(token),
                    "template token {token} was never assigned"
                );
            }
        }
    }
    let mut memory_layout = memory_layout(
        &heap,
        min_free,
        &seed,
        &stats,
        d.rounds,
        output_log2,
        wrap.frontier.0.len(),
        wrap.decoder.setup_cap_image.len(),
        stats.qtable.len(),
        &setup_data,
    );
    let image = heap.regions.iter().find(|r| r.name == "IMAGE").unwrap();
    memory_layout.push_str(&preimage.markdown(image.start));
    memory_layout.push_str(&format!(
        "\n## Runtime code layout\n\nLet `C = codesize()` and `S = C - SETUP_DATA_BYTES`. The setup data occupies the last {} bytes (`{:#x}`) of the deployed code. Its internal offsets above are relative to `S`. Endpoints are exclusive.\n\n| Section | Start | Size | End |\n| --- | --- | --- | --- |\n| Verifier code, including Solidity metadata | 0 | `S` | `S` |\n| Setup data | `S` | `SETUP_DATA_BYTES` | `C` |\n\nThere is no registry suffix. `test_create_requires_glamsterdam_size_limit` reports the actual deployed runtime size and checks the code-size limits. `test_embedded_setup_matches_reference` checks the byte-exact runtime prefix against `type(GkrWhirVerifierCode).runtimeCode`, the setup length and its pinned hash.\n",
        setup_data.len(), setup_data.len(),
    ));
    (out, setup_data, memory_layout)
}

/// SEED owns the transcript seed, every seed-relative absorb, then the circuit cache.
struct SeedLayout {
    absorb_end: usize,
    cache_offset: usize,
    bytes: usize,
}

impl SeedLayout {
    fn from(stats: &CircuitYulStats) -> Self {
        // transcript_4to1_dual hashes [0,96), PoW [0,40), draws [0,32).
        // Cache-free layers copy their claims at +32 and hash max_seed_absorb_bytes.
        let absorbs = [32, 40, 96, stats.max_seed_absorb_bytes];
        let absorb_end = *absorbs.iter().max().unwrap();
        let cache_offset = absorb_end.next_multiple_of(32);
        let cache_end = cache_offset + 32 * stats.max_cache_slots;
        for end in absorbs {
            assert!(end <= cache_offset, "seed absorb overlaps circuit cache");
        }
        Self {
            absorb_end,
            cache_offset,
            bytes: absorb_end.max(cache_end),
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn memory_layout(
    heap: &HeapAlloc,
    min_free: u128,
    seed: &SeedLayout,
    stats: &CircuitYulStats,
    rounds: usize,
    output_log2: usize,
    frontier_bytes: usize,
    cap_bytes: usize,
    qtable_bytes: usize,
    setup_data: &[u8],
) -> String {
    use sha3::{Digest, Keccak256};
    use std::fmt::Write;
    let number = |v: u128| format!("{v} / `{v:#x}`");
    let mut out = String::from("# Generated wrap verifier memory layout\n\nGenerated by `cargo test -p verifier_evm --release --test generate_contracts -- --ignored`.\nDo not edit: region sizes, accessors and purposes come from the generator.\nAll ranges are byte offsets with exclusive ends; addresses and sizes are decimal / hex.\n\n## Reserved memory and spill guard\n\n| Area / slot | Start | Size | End | Purpose |\n| --- | ---: | ---: | ---: | --- |\n| Solidity scratch | 0 / `0x0` | 64 / `0x40` | 64 / `0x40` | Hashing scratch |\n| Free-memory pointer | 64 / `0x40` | 32 / `0x20` | 96 / `0x60` | Solidity allocation cursor |\n| Zero slot | 96 / `0x60` | 32 / `0x20` | 128 / `0x80` | Solidity reserved zero word |\n");
    writeln!(
        out,
        "| via_ir spill zone | {} | {} | {} | Compiler stack spills |",
        number(128),
        number(min_free - 128),
        number(min_free)
    )
    .unwrap();
    for (i, name, purpose) in [
        (0, "P_PTR", "Field modulus"),
        (1, "CIRCUIT_PTR", "Circuit-layer image cursor"),
        (2, "SETUP_CODE_OFFSET_PTR", "Appended setup code offset"),
    ] {
        let start = min_free + 32 * i;
        writeln!(
            out,
            "| `{name}` | {} | {} | {} | {purpose} |",
            number(start),
            number(32),
            number(start + 32)
        )
        .unwrap();
    }
    writeln!(out, "\nThe fallback rejects `mload(0x40) > MINIMUM_FREE_HEAP_PTR` ({}) before decoding or proof verification. All fixed slots and heap regions begin at or above that limit.\n\n## Heap allocations\n\n| Region | Accessor / constant | Start | Size | End | Purpose |\n| --- | --- | ---: | ---: | ---: | --- |", number(min_free)).unwrap();
    for r in &heap.regions {
        writeln!(
            out,
            "| {} | `{}` | {} | {} | {} | {} |",
            r.name,
            r.accessor,
            number(r.start),
            number(r.size.value),
            number(r.start + r.size.value),
            r.purpose
        )
        .unwrap();
    }
    writeln!(out, "\nHeap end: {}.\n\n## SEED word layout\n\nOffsets below are relative to `SEED_PTR()`.\n\n| Use | Start | Size | End |\n| --- | ---: | ---: | ---: |\n| Transcript seed | {} | {} | {} |\n| Absorb scratch | {} | {} | {} |\n| Circuit cache ({} words) | {} | {} | {} |",
        number(heap.next), number(0), number(32), number(32), number(32), number((seed.cache_offset-32) as u128), number(seed.cache_offset as u128),
        stats.max_cache_slots, number(seed.cache_offset as u128), number((32*stats.max_cache_slots) as u128), number((seed.cache_offset+32*stats.max_cache_slots) as u128)).unwrap();
    writeln!(out, "\nDraws hash 32 bytes, PoW absorbs 40 bytes, and `transcript_4to1_dual` absorbs 96 bytes from SEED. Cache-free claims batches copy at SEED+32 and absorb at most {} bytes including the seed. {} The maximum absorb end is {}; the generated cache offset is its word-aligned ceiling ({}). The generator asserts each seed-relative absorb ends before the cache. SEED size is the word-aligned `max(absorb_end, cache_offset + 32 * max_cache_slots)` = {}.\n\n## POINT sizing\n\nPOINT contains exactly {rounds} words ({} bytes), with zero slack. Initialization writes indices 0..{}; the {} dim-reducing layers use `fs = {output_log2} + k` and shift up through index `fs`, whose maximum is {}. Circuit sumchecks rewrite indices 0..{}. The generator checks the template write-loop bounds and asserts `POINT_BYTES == 32 * (largest_written_index + 1)`; the next word belongs to SEED.\n\n## Appended setup construction\n\nThe no-argument constructor returns `type(GkrWhirVerifierCode).runtimeCode || setup data`. Glamsterdam's EIP-7954 code-size limit permits this single-contract layout; verification reads setup with `codecopy`, without an external data contract. The registry is a generated constant and requires regeneration when changed.\n\nThe setup starts at `codesize() - SETUP_DATA_BYTES`: Solidity metadata is inside the runtime prefix, so its length cannot shift these tail-relative reads. A toolchain that appends bytes after the constructor's returned array breaks this assumption; `test_embedded_setup_matches_reference` checks exact deployed prefix and setup bytes, and `test_rejects_shifted_setup` rejects a displaced tail. Changing setup length without regenerating breaks offsets; the generator's pinned payload hash/length assertions, the deployed hash/length check, and the canonical proof test cover that mismatch. `test_rejects_altered_setup_data` separately covers frontier, cap and term-table corruption.\n\n## Setup internal offsets\n\nOffsets are relative to the setup start in runtime code.\n\n| Section | Start | Size | End |\n| --- | ---: | ---: | ---: |",
        number(stats.max_seed_absorb_bytes as u128), if stats.max_seed_absorb_bytes == 0 { "No layer of the current circuit emits that cache-free claims-batch path." } else { "The current circuit emits that cache-free claims-batch path." },
        number(seed.absorb_end as u128), number(seed.cache_offset as u128), number(seed.bytes.next_multiple_of(32) as u128),
        32*rounds, output_log2-1, rounds-output_log2, rounds-1, rounds-1).unwrap();
    let mut start = 0;
    for (name, size) in [
        ("STOP", 1),
        ("Setup frontier", frontier_bytes),
        ("Setup cap image", cap_bytes),
        ("GKR term table", qtable_bytes),
    ] {
        writeln!(
            out,
            "| {name} | {} | {} | {} |",
            number(start as u128),
            number(size as u128),
            number((start + size) as u128)
        )
        .unwrap();
        start += size;
    }
    assert_eq!(start, setup_data.len());
    writeln!(
        out,
        "\nSetup total: {} bytes. Pinned Keccak256: `{}`.\n",
        number(start as u128),
        hex_bytes(&Keccak256::digest(setup_data))
    )
    .unwrap();
    out
}

/// The GKR heap regions `(gkr.sol constant suffix, Yul accessor name, padded size as a
/// readable expression)` in allocation order (= the template's accessor chain order), every
/// size derived from the circuit / config and the emitted circuit.yul (see each entry).
fn gkr_heap_regions(
    d: &Derived,
    stats: &CircuitYulStats,
    init_bytes: &Lit,
    output_evals: usize,
    pack: usize,
    image_bytes: usize,
) -> Vec<(&'static str, &'static str, Lit, &'static str)> {
    let seed = SeedLayout::from(stats);
    // Absorb scratch: gkr_init's 32 + INIT_BYTES, the circuit layers' claims-batch absorbs, and
    // emit_gkr_mark's sub-buffers (packing coords, merged claims, whir_fold_pack's PACK-slot
    // chunk buffer — the generated HANDOFF offsets, one word each).
    let pack_log2 = pack.trailing_zeros() as usize;
    let handoff_bytes = 32 * (pack_log2 + d.merged_mw + d.setup_merged + pack);
    let abs_bytes = if 32 + init_bytes.value as usize >= stats.max_absorb_bytes.max(handoff_bytes) {
        Lit::num(32).add(init_bytes) // the seed word + gkr_init's output-evals absorb
    } else {
        words_for(stats.max_absorb_bytes.max(handoff_bytes))
    };
    let w = |n: usize| Lit::words(n as u128);
    let regions = vec![
        (
            "MEMORY_CHALLS",
            "MEMORY_CHALLS_PTR",
            w(7),
            "Permutation linearization challenges",
        ), // 6 perm-linearization challenges + additive
        (
            "LOGUP_CHALLS",
            "LOGUP_CHALLS_PTR",
            w(2),
            "Lookup batching challenges",
        ), // alpha, additive
        (
            "POINT",
            "POINT_PTR",
            w(d.rounds),
            "GKR claim-point coordinates",
        ), // the claim point grows to trace_log2 coords
        (
            "SEED",
            "SEED_PTR",
            words_for(seed.bytes),
            "Transcript seed, absorb scratch and disjoint circuit cache",
        ),
        (
            "BATCHING",
            "GKR_BATCHING_PTR",
            Lit::num(32),
            "Dimension-reduction batching challenge",
        ),
        (
            "CLAIMS",
            "GKR_CLAIMS_PTR",
            w(d.num_outputs),
            "Dimension-reduction output claims",
        ),
        // eq[OUTPUT_EVALS] for the entry claims; reused as SI[NUM_OUTPUTS] by gkr_dr_final
        (
            "EQ",
            "GKR_EQ_PTR",
            w(output_evals.max(d.num_outputs)),
            "Output equality weights; boundary sorted indices",
        ),
        (
            "ABS",
            "GKR_ABS_PTR",
            abs_bytes,
            "Transcript absorbs and GKR to WHIR handoff scratch",
        ),
        (
            "CIRCUIT_CLAIMS",
            "GKR_CIRCUIT_CLAIMS_PTR",
            w(stats.max_claims_slots),
            "Circuit-layer at-point evaluations",
        ),
        (
            "GATEVAL",
            "GKR_GATEVAL_PTR",
            w(stats.gateval_slots),
            "Layer-0 gate accumulators",
        ),
        (
            "QTABLE",
            "GKR_QTABLE_PTR",
            words_for(stats.qtable.len()),
            "Packed layer-0 term table",
        ),
        // The decoded GKR image.
        (
            "IMAGE",
            "IMAGE_PTR",
            words_for(image_bytes),
            "Decoded GKR calldata image",
        ),
    ];
    regions
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
//    overlaps; the WHIR half never touches 0x40/0x60, so the single spill guard before the GKR
//    half covers both halves.

/// `__TEMPLATE_WHIR_*` names the GKR template references (handoff) — must come from whir.sol.
const GKR_REQUIRED_WHIR_CONSTS: &[&str] = &[
    "__TEMPLATE_WHIR_SEED_PTR",
    "__TEMPLATE_WHIR_GAMMA_PTR",
    "__TEMPLATE_WHIR_REG_CLAIM",
    "__TEMPLATE_WHIR_Z_PTR",
    "__TEMPLATE_WHIR_BCAP0_PTR",
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
        if name.starts_with("__TEMPLATE_") {
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
    for HeapRegion {
        name, start, size, ..
    } in &heap.regions
    {
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
