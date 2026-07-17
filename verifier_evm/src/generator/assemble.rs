//! Assemble full verifier Solidity from the circuit artifact + caller-supplied params.
//!
//! The GKR verifier is the hand-written `gkr.sol` template with the circuit-specific
//! `circuit.yul` inlined at `// __INLINE_CIRCUIT_YUL__` and its circuit-derived `constant`s
//! substituted. Everything the generator needs about the *circuit* comes from the artifact;
//! the two genuinely non-circuit values (PoW difficulty, program terminal PC) are parameters.
//!
//! A handful of WHIR *proving-config* constants (`WHIR_PACK_LOG2`, `WHIR_CAP`, the WHIR
//! round/fold/query schedule) are not encoded in the circuit artifact; they track the single
//! supported WHIR proving configuration and are baked here / in the whir.sol template.

use super::{emit_circuit_yul, GeneratedContracts};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;

const GKR_TEMPLATE: &str = include_str!("../templates/gkr.sol");
const WHIR_TEMPLATE: &str = include_str!("../templates/whir.sol");
const REGISTRY_TEMPLATE: &str = include_str!("../templates/GkrWhirRegistry.sol");

/// Marker in `gkr.sol` where the generated `circuit.yul` is spliced.
const INLINE_MARKER: &str = "// __INLINE_CIRCUIT_YUL__";

// WHIR proving-config constants (the single supported configuration). Not derivable from the
// circuit artifact; must match the whir.sol verifier + the prover's WHIR schedule.
const WHIR_PACK_LOG2: u128 = 4;
const WHIR_CAP: u128 = 8; // base-oracle merkle-cap size (2^CAP_LOG2)

/// Replace the RHS of the single `uint256 constant <name> = <...>;` line with `= <value>;`,
/// preserving indentation and any trailing `// comment`. Panics unless exactly one such line
/// exists, so a template rename can never silently drop a substitution.
fn set_const(src: &str, name: &str, value: u128) -> String {
    let needle = format!("constant {name} "); // name is followed by alignment whitespace then '='
    let mut hits = 0usize;
    let body: Vec<String> = src
        .lines()
        .map(|line| {
            if line.trim_start().starts_with("uint256 constant ") && line.contains(&needle) {
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
    assert_eq!(hits, 1, "expected exactly one `uint256 constant {name}` line in the template");
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
    let cut = src.find(&needle).unwrap_or_else(|| panic!("template missing `{needle}`"));
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

/// Generate the GKR + WHIR + Registry Solidity for `circuit`. Uses only the circuit artifact
/// plus the caller-supplied PoW difficulties and program terminal PC.
pub fn generate_verifiers(
    circuit: &GKRCircuitArtifact<Proth120>,
    external_pow_bits: u32,
    whir_batch_pow_bits: u32,
    final_pc: u32,
) -> GeneratedContracts {
    let d = Derived::from(circuit);
    // registers(384) + final_pc(12) + top_bits(num_teardown_sets * 4) + setup_cap + memory_cap
    let preimage_bytes = 384 + 12 + d.num_teardown_sets * 4 + 2 * WHIR_CAP * 32;
    let caps_bytes = 2 * WHIR_CAP * 32;

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
        ("__TEMPLATE_WHIR_MERGED_MW", d.merged_mw),
        ("__TEMPLATE_WHIR_PACK_LOG2", WHIR_PACK_LOG2),
        ("__TEMPLATE_WHIR_Z_COORDS", d.rounds + WHIR_PACK_LOG2),
        ("__TEMPLATE_WHIR_BASE_Z_COORDS", d.rounds),
        ("__TEMPLATE_WHIR_CAP", WHIR_CAP),
        ("__TEMPLATE_MERKLE_TREE_CAPS_BYTES", caps_bytes),
        ("__TEMPLATE_GKR_INIT_PREIMAGE_BYTES", preimage_bytes),
        ("__TEMPLATE_EXTERNAL_POW_BITS", external_pow_bits as u128),
        ("__TEMPLATE_WHIR_BATCH_POW_BITS", whir_batch_pow_bits as u128),
        ("__TEMPLATE_EXPECTED_FINAL_PC", final_pc as u128),
    ] {
        gkr = set_const(&gkr, name, value);
    }

    // Drop the trailing test/bench harness (GKRVerifierTest + the via_ir-only GKRStreamGen) so
    // the production source is just `contract GKRVerifier` and compiles under the legacy backend.
    let gkr = strip_from_contract(&gkr, "GKRVerifierTest");

    // 2. WHIR verifier: substitute the artifact/config-derivable cap size; the round/fold/query
    //    schedule stays baked in the template (the single supported WHIR proving configuration).
    let mut whir = set_const(WHIR_TEMPLATE, "CAP", WHIR_CAP);
    whir = set_const(&whir, "CAP_LOG2", WHIR_CAP.trailing_zeros() as u128);
    let whir = strip_from_contract(&whir, "WhirRealProofTest");

    GeneratedContracts {
        gkr_sol: gkr,
        whir_sol: whir,
        registry_sol: REGISTRY_TEMPLATE.to_string(),
    }
}
