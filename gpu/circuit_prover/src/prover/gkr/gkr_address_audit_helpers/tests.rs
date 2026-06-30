use std::path::PathBuf;
use std::sync::Once;

use super::*;
use crate::upstream::BabyBearField;

static LOGGER_INIT: Once = Once::new();

fn init_logger() {
    LOGGER_INIT.call_once(|| {
        let _ = env_logger::Builder::from_default_env()
            .filter_level(log::LevelFilter::Info)
            .is_test(true)
            .try_init();
    });
}

fn artifact_path(relative: &str) -> PathBuf {
    // Workspace-root-relative paths; crate is at gpu/circuit_prover/, so two "..".
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join(relative)
}

fn load_artifact(relative: &str) -> GKRCircuitArtifact<BabyBearField> {
    let f = std::fs::File::open(artifact_path(relative))
        .unwrap_or_else(|e| panic!("opening {}: {}", relative, e));
    serde_json::from_reader(f).unwrap_or_else(|e| panic!("parsing {}: {}", relative, e))
}

/// All committed circuit layouts under `cs/compiled_circuits/`. A new
/// circuit MUST be added here so the audit covers it. The audit
/// enumerates the cached + no-cache pair for every entry so missing
/// modes show up at the top of the test output.
const CIRCUIT_BASENAMES: &[&str] = &[
    "add_sub_lui_auipc_mop",
    "bigint_with_extended_control",
    "blake2_g_function",
    "blake2_with_extended_control",
    "inits_and_teardowns_preprocessed",
    "jump_branch_slt",
    "keccak_special5",
    "mem_subword_only",
    "mem_word_only",
    "shift_binop",
    "unified_reduced_machine",
    "unsigned_mul_div",
];

/// Measurement pass. Walks every layout JSON in
/// `cs/compiled_circuits/` (cached + no-cache), audits per-layer
/// structural counts against the locked ceilings, and reports
/// post-compaction descriptor sizes against the 32 KB inline kernel-arg
/// ceiling.
///
/// Run with `RUST_LOG=info cargo test -p circuit_prover --lib gkr_address_audit -- --nocapture`
/// to see the full per-layer dump.
#[test]
fn gkr_address_audit() {
    init_logger();

    let sizes = projected_post_compaction_sizes();
    log_post_compaction_sizes(&sizes);
    if let Err(msg) = check_descriptor_sizes_under_hard_ceiling(&sizes) {
        panic!("audit abort: descriptor size exceeds 32 KB hard ceiling: {msg}");
    }

    let mut audited = Vec::new();
    let mut errors: Vec<String> = Vec::new();
    let mut global_term_max = super::FlatRound0TermCounts::default();
    let mut global_combined_claim_pair_max: usize = 0;
    let mut global_combined_claim_max_circuit = String::new();
    let mut global_combined_claim_max_layer: usize = 0;
    let mut global_gather_num_addresses_max: usize = 0;
    let mut global_gather_max_circuit = String::new();
    let mut global_gather_max_layer: usize = 0;

    for base in CIRCUIT_BASENAMES.iter() {
        for (suffix, mode_label) in [("_layout_gkr.json", "cached")] {
            let rel = format!("cs/compiled_circuits/{}{}", base, suffix);
            let path = artifact_path(&rel);
            if !path.exists() {
                log::warn!("[gkr-audit] missing {} ({})", rel, mode_label);
                continue;
            }
            let artifact = load_artifact(&rel);
            let name = format!("{} [{}]", base, mode_label);
            let audit = audit_circuit(&name, &artifact);
            log_circuit_audit(&audit);
            if let Err(e) = check_audit_against_budgets(&audit) {
                errors.push(format!("{}", e));
            }
            let circuit_term_max = project_circuit_flat_round0_term_counts(&name, &artifact);
            global_term_max.merge_max(&circuit_term_max);
            let (circuit_pair_max, circuit_pair_max_layer) =
                project_circuit_main_combined_claim_pair_max(&name, &artifact);
            if circuit_pair_max > global_combined_claim_pair_max {
                global_combined_claim_pair_max = circuit_pair_max;
                global_combined_claim_max_circuit = name.clone();
                global_combined_claim_max_layer = circuit_pair_max_layer;
            }
            let (circuit_gather_max, circuit_gather_max_layer) =
                project_circuit_main_gather_num_addresses_max(&name, &artifact);
            if circuit_gather_max > global_gather_num_addresses_max {
                global_gather_num_addresses_max = circuit_gather_max;
                global_gather_max_circuit = name.clone();
                global_gather_max_layer = circuit_gather_max_layer;
            }
            let _ = project_circuit_flat_recipe_audit(&name, &artifact);
            audited.push(audit);
        }
    }

    log::info!(
        "[gkr-audit] audited {} circuit/mode combinations",
        audited.len(),
    );
    log::info!(
        "[gkr-audit] flat round-0 term-count max across all circuits/layers: \
             c0_bf={} c0_ext={} c1_bf_bf={} c1_e4_e4={} c1_bf_e4={} c1_linear={}",
        global_term_max.c0_bf,
        global_term_max.c0_ext,
        global_term_max.c1_bf_bf,
        global_term_max.c1_e4_e4,
        global_term_max.c1_bf_e4,
        global_term_max.c1_linear,
    );
    log::info!(
        "[gkr-audit] main-layer combined_claim_desc_pairs max across all circuits: \
             {} u32 entries = {} bytes (circuit={}, layer={})",
        global_combined_claim_pair_max,
        global_combined_claim_pair_max * 4,
        global_combined_claim_max_circuit,
        global_combined_claim_max_layer,
    );
    let combined_claim_pair_count = global_combined_claim_pair_max / 2;
    if combined_claim_pair_count > super::GKR_COMBINED_CLAIM_MAX_PAIRS {
        errors.push(format!(
            "{}: combined_claim_desc_pairs has {} pairs ({} u32 entries) — exceeds \
                 GKR_COMBINED_CLAIM_MAX_PAIRS = {} (layer {})",
            global_combined_claim_max_circuit,
            combined_claim_pair_count,
            global_combined_claim_pair_max,
            super::GKR_COMBINED_CLAIM_MAX_PAIRS,
            global_combined_claim_max_layer,
        ));
    }

    log::info!(
        "[gkr-audit] main-layer gather num_addresses max across all circuits: \
             {} ({} B src_ptrs) (circuit={}, layer={})",
        global_gather_num_addresses_max,
        global_gather_num_addresses_max * 8,
        global_gather_max_circuit,
        global_gather_max_layer,
    );
    if global_gather_num_addresses_max > super::GKR_GATHER_MAX_ADDRESSES {
        errors.push(format!(
            "{}: main-layer gather has {} distinct addresses — exceeds \
                 GKR_GATHER_MAX_ADDRESSES = {} (layer {})",
            global_gather_max_circuit,
            global_gather_num_addresses_max,
            super::GKR_GATHER_MAX_ADDRESSES,
            global_gather_max_layer,
        ));
    }

    if !errors.is_empty() {
        panic!(
            "audit abort: {} circuit(s) exceed locked budgets:\n{}",
            errors.len(),
            errors.join("\n"),
        );
    }
}

/// Walk every layer of a circuit, build the same kernel blueprints the
/// production prover does (CPU-only via the `is_base_field_at_layer`
/// closure), then project the per-layer flat round-0 term counts. Returns
/// the per-circuit max across layers; the test merges into a global max.
fn project_circuit_flat_round0_term_counts(
    circuit_name: &str,
    artifact: &cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
) -> super::FlatRound0TermCounts {
    use crate::prover::gkr::backward::{
        build_main_layer_kernel_blueprints_static, canonical_inits_and_teardowns_top_bits,
    };
    use crate::prover::gkr::storage_layout::{FieldType, GpuGKRStorageLayout};
    use field::baby_bear::ext4::BabyBearExt4;
    use prover::definitions::GKRExternalChallenges;
    use prover::gkr::high_bits_offset_for_inits_and_teardowns;

    let layout = GpuGKRStorageLayout::from_artifact(artifact);
    let inits_top_bits =
        canonical_inits_and_teardowns_top_bits(artifact.memory_layout.teardown_sets.len());
    let inits_high_bits_shift = if artifact.memory_layout.teardown_sets.is_empty() {
        0
    } else {
        high_bits_offset_for_inits_and_teardowns::<2>(artifact.trace_len)
    };
    let external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4>::default();

    let mut circuit_max = super::FlatRound0TermCounts::default();
    for (layer_idx, layer) in artifact.layers.iter().enumerate() {
        // Skip layers that use relations the GPU main-layer dispatch
        // doesn't implement. The static blueprint builder panics on these,
        // and circuits containing them aren't currently GPU-provable.
        if layer_has_unsupported_relations(layer) {
            log::warn!(
                "[gkr-audit] {} layer {} has unsupported relations; skipping term-count projection",
                circuit_name,
                layer_idx,
            );
            continue;
        }
        let is_base_field_at_layer = |addr: &cs::definitions::GKRAddress| -> bool {
            layout
                .layers
                .get(layer_idx)
                .and_then(|l| l.lookup(addr))
                .map(|(_, ft, _)| ft == FieldType::Base)
                .unwrap_or(false)
        };
        let blueprints = build_main_layer_kernel_blueprints_static::<BabyBearExt4>(
            layer,
            layer_idx,
            &is_base_field_at_layer,
            &external_challenges,
            &inits_top_bits,
            inits_high_bits_shift,
            artifact.memory_layout.total_width,
            artifact.witness_layout.total_width,
        );
        let layer_counts = super::project_layer_flat_round0_term_counts(&blueprints);
        log::debug!(
                "[gkr-audit] {} layer {}: c0_bf={} c0_ext={} c1_bf_bf={} c1_e4_e4={} c1_bf_e4={} c1_linear={}",
                circuit_name,
                layer_idx,
                layer_counts.c0_bf,
                layer_counts.c0_ext,
                layer_counts.c1_bf_bf,
                layer_counts.c1_e4_e4,
                layer_counts.c1_bf_e4,
                layer_counts.c1_linear,
            );
        circuit_max.merge_max(&layer_counts);
    }
    log::info!(
            "[gkr-audit] {} flat round-0 term-count max: c0_bf={} c0_ext={} c1_bf_bf={} c1_e4_e4={} c1_bf_e4={} c1_linear={}",
            circuit_name,
            circuit_max.c0_bf,
            circuit_max.c0_ext,
            circuit_max.c1_bf_bf,
            circuit_max.c1_e4_e4,
            circuit_max.c1_bf_e4,
            circuit_max.c1_linear,
        );
    circuit_max
}

/// Walk every supported main-layer of a circuit, build the same blueprints
/// the production prover does, and compute the per-layer
/// `combined_claim_desc_pairs` u32 entry count. Returns
/// `(max_entries, layer_idx_at_max)`.
fn project_circuit_main_combined_claim_pair_max(
    circuit_name: &str,
    artifact: &cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
) -> (usize, usize) {
    use crate::prover::gkr::backward::{
        build_main_layer_kernel_blueprints_static, canonical_inits_and_teardowns_top_bits,
    };
    use crate::prover::gkr::storage_layout::{FieldType, GpuGKRStorageLayout};
    use field::baby_bear::ext4::BabyBearExt4;
    use prover::definitions::GKRExternalChallenges;
    use prover::gkr::high_bits_offset_for_inits_and_teardowns;

    let layout = GpuGKRStorageLayout::from_artifact(artifact);
    let inits_top_bits =
        canonical_inits_and_teardowns_top_bits(artifact.memory_layout.teardown_sets.len());
    let inits_high_bits_shift = if artifact.memory_layout.teardown_sets.is_empty() {
        0
    } else {
        high_bits_offset_for_inits_and_teardowns::<2>(artifact.trace_len)
    };
    let external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4>::default();

    let mut max_entries: usize = 0;
    let mut max_layer: usize = 0;
    for (layer_idx, layer) in artifact.layers.iter().enumerate() {
        if layer_has_unsupported_relations(layer) {
            continue;
        }
        let is_base_field_at_layer = |addr: &cs::definitions::GKRAddress| -> bool {
            layout
                .layers
                .get(layer_idx)
                .and_then(|l| l.lookup(addr))
                .map(|(_, ft, _)| ft == FieldType::Base)
                .unwrap_or(false)
        };
        let blueprints = build_main_layer_kernel_blueprints_static::<BabyBearExt4>(
            layer,
            layer_idx,
            &is_base_field_at_layer,
            &external_challenges,
            &inits_top_bits,
            inits_high_bits_shift,
            artifact.memory_layout.total_width,
            artifact.witness_layout.total_width,
        );
        let entries = super::project_layer_main_combined_claim_pair_count(&blueprints);
        log::debug!(
            "[gkr-audit] {} layer {}: combined_claim_desc_pairs={} u32 ({} B)",
            circuit_name,
            layer_idx,
            entries,
            entries * 4,
        );
        if entries > max_entries {
            max_entries = entries;
            max_layer = layer_idx;
        }
    }
    log::info!(
        "[gkr-audit] {} main combined_claim_desc_pairs max: {} u32 ({} B) at layer {}",
        circuit_name,
        max_entries,
        max_entries * 4,
        max_layer,
    );
    (max_entries, max_layer)
}

/// Walk every supported main-layer of a circuit and dump the flat round-0
/// recipe audit (recipe count, term count, qt×lt blowup) per layer.
/// Logs at INFO; returns the per-circuit max recipe-count layer.
fn project_circuit_flat_recipe_audit(
    circuit_name: &str,
    artifact: &cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
) -> super::FlatRecipeAudit {
    use crate::prover::gkr::backward::{
        build_main_layer_kernel_blueprints_static, canonical_inits_and_teardowns_top_bits,
    };
    use crate::prover::gkr::eval_recipes::{
        GpuFlatRecipeEvalDesc, FLAT_IMMEDIATE_MAX_MONOMIALS, FLAT_IMMEDIATE_MAX_RECIPES,
        FLAT_RECIPE_MAX_HEADERS, FLAT_RECIPE_MAX_TERMS,
    };
    use crate::prover::gkr::storage_layout::{FieldType, GpuGKRStorageLayout};
    use field::baby_bear::ext4::BabyBearExt4;
    use prover::definitions::GKRExternalChallenges;
    use prover::gkr::high_bits_offset_for_inits_and_teardowns;

    let layout = GpuGKRStorageLayout::from_artifact(artifact);
    let inits_top_bits =
        canonical_inits_and_teardowns_top_bits(artifact.memory_layout.teardown_sets.len());
    let inits_high_bits_shift = if artifact.memory_layout.teardown_sets.is_empty() {
        0
    } else {
        high_bits_offset_for_inits_and_teardowns::<2>(artifact.trace_len)
    };
    // Set distinct non-zero linearization challenges so that the
    // qt.challenge / lt.challenge values produced by the Immediate-path
    // metadata builders end up structurally distinct (same hardcoded form
    // → same E4; different forms → different E4). This gives a tight
    // upper bound on the unique-immediate count.
    let mut external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4>::default();
    use field::baby_bear::ext2::BabyBearExt2;
    let make_e4 = |seed: u32| -> BabyBearExt4 {
        BabyBearExt4 {
            c0: BabyBearExt2 {
                c0: BabyBearField::from_u64_with_reduction((seed as u64) * 1_000_003 + 17),
                c1: BabyBearField::from_u64_with_reduction((seed as u64) * 1_000_003 + 23),
            },
            c1: BabyBearExt2 {
                c0: BabyBearField::from_u64_with_reduction((seed as u64) * 1_000_003 + 31),
                c1: BabyBearField::from_u64_with_reduction((seed as u64) * 1_000_003 + 41),
            },
        }
    };
    for (i, c) in external_challenges
        .permutation_argument_linearization_challenges
        .iter_mut()
        .enumerate()
    {
        *c = make_e4(i as u32 + 1);
    }
    external_challenges.permutation_argument_additive_part = make_e4(1000);

    let mut circuit_max = super::FlatRecipeAudit::default();
    for (layer_idx, layer) in artifact.layers.iter().enumerate() {
        if layer_has_unsupported_relations(layer) {
            continue;
        }
        let is_base_field_at_layer = |addr: &cs::definitions::GKRAddress| -> bool {
            layout
                .layers
                .get(layer_idx)
                .and_then(|l| l.lookup(addr))
                .map(|(_, ft, _)| ft == FieldType::Base)
                .unwrap_or(false)
        };
        let blueprints = build_main_layer_kernel_blueprints_static::<BabyBearExt4>(
            layer,
            layer_idx,
            &is_base_field_at_layer,
            &external_challenges,
            &inits_top_bits,
            inits_high_bits_shift,
            artifact.memory_layout.total_width,
            artifact.witness_layout.total_width,
        );
        let r0 = super::project_layer_flat_round0_recipe_audit(&blueprints);
        let cont = super::project_layer_flat_continuation_recipe_audit(&blueprints);
        let unique_immediates = super::collect_unique_immediates_for_layer(&blueprints);
        let (structural_immediates, structural_monomials) =
            super::collect_structural_immediates_for_layer(&blueprints);
        let r0_bytes = r0.total_recipes as usize * 48 + r0.total_terms as usize * 12;
        let cont_bytes = cont.total_recipes as usize * 48 + cont.total_terms as usize * 12;
        assert!(
            (r0.total_recipes as usize) <= FLAT_RECIPE_MAX_HEADERS,
            "{circuit_name} L{layer_idx}: round-0 recipes exceed inline cap"
        );
        assert!(
            (cont.total_recipes as usize) <= FLAT_RECIPE_MAX_HEADERS,
            "{circuit_name} L{layer_idx}: continuation recipes exceed inline cap"
        );
        assert!(
            (r0.total_terms as usize) <= FLAT_RECIPE_MAX_TERMS,
            "{circuit_name} L{layer_idx}: round-0 terms exceed inline cap"
        );
        assert!(
            (cont.total_terms as usize) <= FLAT_RECIPE_MAX_TERMS,
            "{circuit_name} L{layer_idx}: continuation terms exceed inline cap"
        );
        assert!(
                structural_immediates <= FLAT_IMMEDIATE_MAX_RECIPES,
                "{circuit_name} L{layer_idx}: structural immediate recipes {structural_immediates} exceed inline cap {FLAT_IMMEDIATE_MAX_RECIPES}"
            );
        assert!(
                structural_monomials <= FLAT_IMMEDIATE_MAX_MONOMIALS,
                "{circuit_name} L{layer_idx}: structural immediate monomials {structural_monomials} exceed inline cap {FLAT_IMMEDIATE_MAX_MONOMIALS}"
            );
        assert!(
            std::mem::size_of::<GpuFlatRecipeEvalDesc>() <= 32 * 1024,
            "flat recipe descriptor must stay within the 32 KB kernel argument ceiling"
        );
        log::info!(
            "[gkr-audit] {} L{}  \
                 R0: rec={:>5} (imm={:>5} def={:>4} bare={:>4}) term={:>5} bytes={:>7}  \
                 CONT: rec={:>5} (imm={:>5} def={:>4} bare={:>4}) term={:>5} bytes={:>7}  \
                 unique_imm_E4_values_for_layer={:>5} (+1 for ONE slot, total dev_buf_E4s={:>5})  \
                 structural_imm_recipes={:>4} structural_monomials={:>4}",
            circuit_name,
            layer_idx,
            r0.total_recipes,
            r0.recipes_immediate,
            r0.recipes_deferred,
            r0.recipes_bare,
            r0.total_terms,
            r0_bytes,
            cont.total_recipes,
            cont.recipes_immediate,
            cont.recipes_deferred,
            cont.recipes_bare,
            cont.total_terms,
            cont_bytes,
            unique_immediates.len(),
            unique_immediates.len() + 1,
            structural_immediates,
            structural_monomials,
        );
        circuit_max.merge_max(&r0);
    }
    log::info!(
        "[gkr-audit] {} flat round-0 recipe-audit MAX: \
             recipes={} terms={} xprod_gates={} xprod_expanded={} max_MxN={}",
        circuit_name,
        circuit_max.total_recipes,
        circuit_max.total_terms,
        circuit_max.xprod_gates,
        circuit_max.xprod_expanded_recipes,
        circuit_max.xprod_max_m_times_n,
    );
    circuit_max
}

/// Walk every supported main-layer of a circuit, build the same blueprints
/// the production prover does, and compute the per-layer
/// `gather_e_addresses` payload size (distinct, non-placeholder addresses
/// across kernel `inputs_in_base ∪ inputs_in_extension`).
/// Returns `(max_addresses, layer_idx_at_max)`.
fn project_circuit_main_gather_num_addresses_max(
    circuit_name: &str,
    artifact: &cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
) -> (usize, usize) {
    use crate::prover::gkr::backward::{
        build_main_layer_kernel_blueprints_static, canonical_inits_and_teardowns_top_bits,
    };
    use crate::prover::gkr::storage_layout::{FieldType, GpuGKRStorageLayout};
    use field::baby_bear::ext4::BabyBearExt4;
    use prover::definitions::GKRExternalChallenges;
    use prover::gkr::high_bits_offset_for_inits_and_teardowns;

    let layout = GpuGKRStorageLayout::from_artifact(artifact);
    let inits_top_bits =
        canonical_inits_and_teardowns_top_bits(artifact.memory_layout.teardown_sets.len());
    let inits_high_bits_shift = if artifact.memory_layout.teardown_sets.is_empty() {
        0
    } else {
        high_bits_offset_for_inits_and_teardowns::<2>(artifact.trace_len)
    };
    let external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4>::default();

    let mut max_addresses: usize = 0;
    let mut max_layer: usize = 0;
    for (layer_idx, layer) in artifact.layers.iter().enumerate() {
        if layer_has_unsupported_relations(layer) {
            continue;
        }
        let is_base_field_at_layer = |addr: &cs::definitions::GKRAddress| -> bool {
            layout
                .layers
                .get(layer_idx)
                .and_then(|l| l.lookup(addr))
                .map(|(_, ft, _)| ft == FieldType::Base)
                .unwrap_or(false)
        };
        let blueprints = build_main_layer_kernel_blueprints_static::<BabyBearExt4>(
            layer,
            layer_idx,
            &is_base_field_at_layer,
            &external_challenges,
            &inits_top_bits,
            inits_high_bits_shift,
            artifact.memory_layout.total_width,
            artifact.witness_layout.total_width,
        );
        let n = super::project_layer_main_gather_num_addresses(&blueprints);
        log::debug!(
            "[gkr-audit] {} layer {}: gather num_addresses={}",
            circuit_name,
            layer_idx,
            n,
        );
        if n > max_addresses {
            max_addresses = n;
            max_layer = layer_idx;
        }
    }
    log::info!(
        "[gkr-audit] {} main gather num_addresses max: {} at layer {}",
        circuit_name,
        max_addresses,
        max_layer,
    );
    (max_addresses, max_layer)
}

/// Detect relations the GPU main-layer dispatch doesn't implement. The
/// static blueprint builder panics on these via `unimplemented!()`, and
/// production callers can't process them either — so they're transparent
/// holes in our term-count projection.
fn layer_has_unsupported_relations(layer: &cs::gkr_compiler::GKRLayerDescription) -> bool {
    use cs::gkr_compiler::NoFieldGKRRelation as R;
    layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
        .any(|g| {
            matches!(
                &g.enforced_relation,
                R::MaxQuadratic { .. } | R::UnbalancedGrandProductWithCache { .. }
            ) || matches!(
                &g.enforced_relation,
                R::EnforceConstraintsMaxQuadratic { .. }
            )
        })
}
