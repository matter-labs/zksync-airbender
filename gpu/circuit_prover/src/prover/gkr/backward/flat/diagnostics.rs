//! Human-readable dump for the round-1 flat plan, gated behind the
//! `GPU_PROVER_DUMP_FLAT_PLAN` env var at the call site.

use super::super::kernels::GpuGKRMainLayerKernelPlan;
use super::continuation::{ContinuationSourceAssignment, FlatContinuationBuildPlan};
use super::round12_fused::Round1FusedSources;
use super::types::CoefficientRecipe;
use crate::primitives::field::BF;
use crate::upstream::Field;

/// Format a source index for display: "B3" for base, "E7" for ext.
fn fmt_source(idx: u16, assignments: &[ContinuationSourceAssignment]) -> String {
    let a = assignments
        .iter()
        .find(|a| a.source_table_idx == idx as u32);
    match a {
        Some(a) if a.is_ext => format!("E{}", idx),
        Some(_) => format!("B{}", idx),
        None => format!("?{}", idx),
    }
}

/// Format a coefficient recipe as a short string.
fn fmt_recipe<E: std::fmt::Debug>(recipe: &CoefficientRecipe<E>) -> String {
    let mut s = format!("β^{}", recipe.batch_power);
    if recipe.negate {
        s.push_str(" NEG");
    }
    if !recipe.prefactors.is_empty() {
        s.push_str(&format!(" ×{}pf", recipe.prefactors.len()));
    }
    s
}

/// Dump a human-readable representation of the round 1 flat plan.
/// Called from `prepare_layer_from_blueprints` when `GPU_PROVER_DUMP_FLAT_PLAN` is set.
pub(crate) fn dump_flat_round1_plan<E: Field + field::FieldExtension<BF> + std::fmt::Debug>(
    layer_idx: usize,
    round1_desc: Option<&Round1FusedSources>,
    continuation_plan: Option<&FlatContinuationBuildPlan<E>>,
    kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
) {
    let Some(plan) = continuation_plan else {
        log::info!(
            "=== FLAT ROUND 1 PLAN: layer {} — no continuation plan ===",
            layer_idx
        );
        return;
    };
    let Some(desc) = round1_desc else {
        log::info!(
            "=== FLAT ROUND 1 PLAN: layer {} — no round 1 desc ===",
            layer_idx
        );
        return;
    };

    let td = &plan.term_desc;
    let assignments = &plan.source_assignments;
    let recipes = &plan.recipes;

    log::info!("=== FLAT ROUND 1 PLAN: layer {} ===", layer_idx);
    log::info!(
        "  sources: {} total ({} base, {} ext in round1 desc)",
        td.num_sources,
        desc.num_base_sources,
        desc.num_ext_sources
    );
    log::info!(
        "  terms: {} constants, {} c0_only_linear, {} unified_quadratic, {} unified_linear",
        td.num_constants,
        td.num_c0_only_linear,
        td.num_unified_quadratic,
        td.num_unified_linear
    );
    log::info!("  coefficients: {}", recipes.len());
    log::info!(" ");

    // --- Source table ---
    // Build a map: continuation source_table_idx → (gate_idx, is_ext, input_idx)
    // and determine first_access from round1 desc.
    // The round1 desc has separate base/ext arrays; we need the remap.
    // Reconstruct it: iterate assignments in order, track base/ext count.
    let mut base_count = 0u32;
    let mut ext_count = 0u32;
    // Map continuation source_table_idx → (round1 base_idx or ext_idx, is_ext)
    let mut src_remap: std::collections::HashMap<u32, (u32, bool)> =
        std::collections::HashMap::new();
    for a in assignments {
        if !src_remap.contains_key(&a.source_table_idx) {
            if a.is_ext {
                src_remap.insert(a.source_table_idx, (ext_count, true));
                ext_count += 1;
            } else {
                src_remap.insert(a.source_table_idx, (base_count, false));
                base_count += 1;
            }
        }
    }

    log::info!("--- SOURCES ---");
    // Print by continuation source_table_idx order
    let mut src_indices: Vec<u32> = src_remap.keys().copied().collect();
    src_indices.sort();
    for &sidx in &src_indices {
        let (round1_idx, is_ext) = src_remap[&sidx];
        let a = assignments
            .iter()
            .find(|a| a.source_table_idx == sidx)
            .unwrap();
        let gate_kind = kernel_plans[a.gate_idx].kind;
        let first_access = if is_ext {
            let r1idx = round1_idx as usize;
            if r1idx < desc.num_ext_sources as usize {
                !desc.ext_sources[r1idx].previous_layer_start.is_null()
            } else {
                false
            }
        } else {
            let r1idx = round1_idx as usize;
            if r1idx < desc.num_base_sources as usize {
                desc.base_sources[r1idx].first_access
            } else {
                false
            }
        };
        let tag = if is_ext { "E" } else { "B" };
        let fa = if first_access { " FIRST_ACCESS" } else { "" };
        let kind_info = if !is_ext {
            let r1idx = round1_idx as usize;
            if r1idx < desc.num_base_sources as usize {
                format!(" kind={:?}", desc.base_sources[r1idx].source_kind)
            } else {
                String::new()
            }
        } else {
            String::new()
        };
        log::info!(
            "  [{tag}{sidx}] gate={gate_kind:?}(#{gate}) input={input}{kind_info}{fa}",
            gate = a.gate_idx,
            input = a.input_idx,
        );
    }
    log::info!(" ");

    // --- Terms by category ---
    // Recipes are ordered: constants, c0_only_linear, unified_quadratic, unified_linear
    let mut recipe_idx = 0usize;

    log::info!("--- CONSTANTS ({}) ---", td.num_constants);
    for i in 0..td.num_constants as usize {
        let r = &recipes[recipe_idx];
        log::info!("  [{i}] {}", fmt_recipe(r));
        recipe_idx += 1;
    }
    if td.num_constants > 0 {
        log::info!(" ");
    }

    log::info!("--- C0_ONLY_LINEAR ({}) ---", td.num_c0_only_linear);
    for i in 0..td.num_c0_only_linear as usize {
        let src = td.c0_only_linear[i].source_idx;
        let r = &recipes[recipe_idx];
        log::info!(
            "  [{i}] src={} {}",
            fmt_source(src, assignments),
            fmt_recipe(r),
        );
        recipe_idx += 1;
    }
    if td.num_c0_only_linear > 0 {
        log::info!(" ");
    }

    log::info!("--- UNIFIED_QUADRATIC ({}) ---", td.num_unified_quadratic);
    for i in 0..td.num_unified_quadratic as usize {
        let t = td.unified_quadratic[i];
        let r = &recipes[recipe_idx];
        log::info!(
            "  [{i}] src_a={} src_b={} {}",
            fmt_source(t.source_a, assignments),
            fmt_source(t.source_b, assignments),
            fmt_recipe(r),
        );
        recipe_idx += 1;
    }
    if td.num_unified_quadratic > 0 {
        log::info!(" ");
    }

    log::info!("--- UNIFIED_LINEAR ({}) ---", td.num_unified_linear);
    for i in 0..td.num_unified_linear as usize {
        let src = td.unified_linear[i].source_idx;
        let r = &recipes[recipe_idx];
        log::info!(
            "  [{i}] src={} {}",
            fmt_source(src, assignments),
            fmt_recipe(r),
        );
        recipe_idx += 1;
    }
    if td.num_unified_linear > 0 {
        log::info!(" ");
    }

    // --- Source reuse summary ---
    log::info!("--- SOURCE REUSE ---");
    let mut reuse: std::collections::HashMap<u16, Vec<String>> = std::collections::HashMap::new();

    for i in 0..td.num_c0_only_linear as usize {
        reuse
            .entry(td.c0_only_linear[i].source_idx)
            .or_default()
            .push(format!("c0_lin[{i}]"));
    }
    for i in 0..td.num_unified_quadratic as usize {
        let t = td.unified_quadratic[i];
        reuse
            .entry(t.source_a)
            .or_default()
            .push(format!("quad[{i}].a"));
        reuse
            .entry(t.source_b)
            .or_default()
            .push(format!("quad[{i}].b"));
    }
    for i in 0..td.num_unified_linear as usize {
        reuse
            .entry(td.unified_linear[i].source_idx)
            .or_default()
            .push(format!("u_lin[{i}]"));
    }

    let mut reuse_entries: Vec<_> = reuse.into_iter().collect();
    reuse_entries.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then(a.0.cmp(&b.0)));
    for (sidx, refs) in &reuse_entries {
        let (round1_idx, is_ext) = src_remap
            .get(&(*sidx as u32))
            .copied()
            .unwrap_or((0, false));
        let first_access = if is_ext {
            let r1idx = round1_idx as usize;
            r1idx < desc.num_ext_sources as usize
                && !desc.ext_sources[r1idx].previous_layer_start.is_null()
        } else {
            let r1idx = round1_idx as usize;
            r1idx < desc.num_base_sources as usize && desc.base_sources[r1idx].first_access
        };
        let fa = if first_access { " FIRST_ACCESS" } else { "" };
        log::info!(
            "  {} → {} refs: {}{fa}",
            fmt_source(*sidx, assignments),
            refs.len(),
            refs.join(", "),
        );
    }
    log::info!("=== END FLAT ROUND 1 PLAN: layer {} ===", layer_idx);
    log::info!(" ");
}
