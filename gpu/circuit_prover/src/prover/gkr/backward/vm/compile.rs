//! Artifact-certified backward coefficient-ISA fixtures for the GPU tests.
//!
//! Two entry points over one realization path:
//!
//!   * [`load_add_sub_l0_coeff_case`] — `add_sub_lui_auipc_mop` layer 0, the
//!     parity ladder's coordinate; and
//!   * [`load_coeff_case`] — any `(circuit, layer, regime, round, budget)` of the
//!     in-scope corpus, which is what Task 12's budget sweep walks.
//!
//! Both hand back everything a GPU run needs: the semantic [`CoeffLayer`], the
//! encoded u16 program, the source binding, and the paging/placement artefacts
//! behind them.
//!
//! It deliberately goes through `gkr_eval_isa::bwd::coeff::artifact::realize`
//! rather than assembling the pipeline by hand. `realize` runs and *certifies*
//! every stage — `certify_paging_plan`, `certify_cell_liveness`,
//! `certify_source_binding`, `certify_encoding` — so a program that reaches the
//! GPU from here has already passed §12.1-§12.3. A hand-rolled
//! `page -> place -> bind -> encode` chain would skip those certificates and let
//! a malformed program become a kernel bug instead of a compiler error.
//!
//! **One schedule, round-specific bindings.** The term ORDER is selected once per
//! `(regime, budget)` at the regime's own `default_target_depth`, exactly as
//! `compile_coordinate` does. Each round then re-realizes that same order with
//! `PagingRequest::target_depth = round`, which is what moves
//! `CoeffSourceBinding::{target_depth, materialize}` and the first-access
//! assignment to the round under test. Selecting a fresh order per round would
//! test four unrelated schedules instead of one schedule at four depths.

#[cfg(all(test, feature = "bench"))]
use std::path::PathBuf;

#[cfg(all(test, feature = "bench"))]
use cs::gkr_compiler::dag_ir::{bwd_roots, lower_dag, validate, BwdRegime, DagLayer};
#[cfg(all(test, feature = "bench"))]
use gkr_eval_isa::bwd::coeff::artifact::{
    lower_and_price, realize, total_read_floor_bytes, ProgramReport,
};
#[cfg(all(test, feature = "bench"))]
use gkr_eval_isa::bwd::coeff::bind::CoeffSourceBinding;
#[cfg(all(test, feature = "bench"))]
use gkr_eval_isa::bwd::coeff::encode::EncodedProgram;
#[cfg(all(test, feature = "bench"))]
use gkr_eval_isa::bwd::coeff::model::CoeffLayer;
#[cfg(all(test, feature = "bench"))]
use gkr_eval_isa::bwd::coeff::schedule::{select_paged_order, CellBudget, PagingRequest};
#[cfg(all(test, feature = "bench"))]
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;

/// The committed layout the case is compiled from.
#[cfg(all(test, feature = "bench"))]
pub(crate) const ADD_SUB_LAYOUT: &str = "add_sub_lui_auipc_mop_layout_gkr.json";

/// The two other layer-0 coordinates §15 requires a focused sweep for before any
/// default budget policy is set. `add_sub`'s winner is NOT generalized.
#[cfg(all(test, feature = "bench"))]
pub(crate) const KECCAK_LAYOUT: &str = "keccak_special5_layout_gkr.json";
#[cfg(all(test, feature = "bench"))]
pub(crate) const BLAKE2_LAYOUT: &str = "blake2_with_extended_control_layout_gkr.json";

/// The in-scope production corpus: the twelve committed layouts whose backward
/// coordinates `gkr_eval_isa`'s `in_scope` constants are pinned from.
///
/// Same names and same order as `gkr_eval_isa`'s `common::FIXTURES` and the
/// Task-3 census's `MANDATORY_LAYOUTS`, so a sweep row is directly comparable
/// with a census row. `coordinates` asserts the enumeration really reproduces
/// [`in_scope::COORDINATES`], which is a far stronger drift guard than the list
/// itself.
#[cfg(all(test, feature = "bench"))]
pub(crate) const SWEEP_LAYOUTS: [&str; 12] = [
    ADD_SUB_LAYOUT,
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    BLAKE2_LAYOUT,
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    KECCAK_LAYOUT,
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

#[cfg(all(test, feature = "bench"))]
const _: () = assert!(
    SWEEP_LAYOUTS.len() == gkr_eval_isa::bwd::coeff::limits::in_scope::CIRCUITS,
    "the sweep corpus must be the whole in-scope circuit set"
);

#[cfg(all(test, feature = "bench"))]
pub(crate) type CrossFields = std::collections::HashMap<
    cs::gkr_compiler::dag_ir::ReadPlace,
    cs::gkr_compiler::dag_ir::FieldKind,
>;

/// One canonical `(circuit, layer)` of the corpus, with the whole-circuit
/// cross-layer field map its lowering needs.
#[cfg(all(test, feature = "bench"))]
pub(crate) struct CanonicalLayer {
    pub(crate) circuit: &'static str,
    pub(crate) layer: usize,
    pub(crate) canonical: DagLayer,
    pub(crate) cross: CrossFields,
}

/// Every backward-bearing layer of one committed layout.
///
/// A layer with no backward roots proves nothing backward and is not a
/// coordinate; the same filter `gkr_eval_isa`'s corpus and the Task-3 census
/// apply.
#[cfg(all(test, feature = "bench"))]
pub(crate) fn bearing_layers(circuit: &'static str) -> Vec<CanonicalLayer> {
    let path = compiled_circuit_path(circuit);
    let bytes = std::fs::read(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let layout: crate::upstream::GKRCircuitArtifact<crate::primitives::field::BF> =
        serde_json::from_slice(&bytes)
            .unwrap_or_else(|error| panic!("parse {}: {error}", path.display()));
    let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("[{circuit}] lower_dag: {error}"));
    validate(&dag).unwrap_or_else(|error| panic!("[{circuit}] validate: {error}"));
    let cross = build_cross_layer_field_map(&dag);
    dag.layers
        .iter()
        .enumerate()
        .filter(|(_, layer)| !bwd_roots(layer).is_empty())
        .map(|(layer_index, layer)| CanonicalLayer {
            circuit,
            layer: layer_index,
            canonical: layer.clone(),
            cross: cross.clone(),
        })
        .collect()
}

/// The whole in-scope corpus, ascending by `(circuit, layer)`.
#[cfg(all(test, feature = "bench"))]
pub(crate) fn corpus_layers() -> Vec<CanonicalLayer> {
    use rayon::prelude::*;
    let mut layers: Vec<CanonicalLayer> = SWEEP_LAYOUTS
        .par_iter()
        .flat_map_iter(|circuit| bearing_layers(circuit))
        .collect();
    layers.sort_by_key(|entry| (entry.circuit, entry.layer));
    assert_eq!(
        layers.len(),
        gkr_eval_isa::bwd::coeff::limits::in_scope::LAYERS,
        "the enumerated corpus must be the pinned in-scope layer set"
    );
    layers
}

/// The three budgets the whole ladder probes: the minimum, the one it selects in
/// the middle of the range, and the maximum — c16 is where the six-bit lane field
/// saturates (16 cells x 4 lanes = 64 lanes) and where the dynamic shared memory
/// reaches `16 * 16 * 128 = 32,768` bytes per block.
#[cfg(all(test, feature = "bench"))]
pub(crate) const PROBED_BUDGETS: [u8; 3] = [2, 5, 16];

// ── Deterministic coefficient values ────────────────────────────────────────
//
// A compiled `CoeffLayer` carries normalized coefficient RECIPES, not values:
// evaluating them in a round's challenge context is Task 13's job. Every parity
// run therefore needs some deterministic bank, and both the CPU interpreters and
// the GPU launch must evaluate the SAME one — which is why these live here and
// not in either test module.
//
// Four independent base digits per E4, so a BF/E4 width confusion cannot pass by
// coincidence.

#[cfg(all(test, feature = "bench"))]
fn fnv(mut acc: u32, words: &[u32]) -> u32 {
    for word in words {
        for byte in word.to_le_bytes() {
            acc ^= u32::from(byte);
            acc = acc.wrapping_mul(16_777_619);
        }
    }
    acc
}

#[cfg(all(test, feature = "bench"))]
pub(crate) fn digit(tag: u32, a: u32, b: u32) -> crate::primitives::field::BF {
    use crate::upstream::PrimeField;
    crate::primitives::field::BF::from_u32_with_reduction(fnv(2_166_136_261, &[tag, a, b]))
}

#[cfg(all(test, feature = "bench"))]
pub(crate) fn pseudo_ext(tag: u32, a: u32, b: u32) -> crate::primitives::field::E4 {
    crate::primitives::field::E4::from_array_of_base([
        digit(tag, a, b),
        digit(tag ^ 0x11, a, b),
        digit(tag ^ 0x22, a, b),
        digit(tag ^ 0x33, a, b),
    ])
}

/// The evaluated value of one BANKED coefficient recipe.
///
/// Reserved `+1` / `-1` never reach this: the interpreters resolve them
/// internally and the kernel never multiplies by them at all.
#[cfg(all(test, feature = "bench"))]
pub(crate) fn pseudo_coefficient(
    id: gkr_eval_isa::bwd::coeff::model::CoefficientRecipeId,
) -> crate::primitives::field::E4 {
    assert!(
        id.bank_index().is_some(),
        "a reserved coefficient literal must never be looked up in the bank"
    );
    pseudo_ext(0xc0ef, id.0, 0)
}

/// The whole evaluated bank, in coefficient-index order: entry `i` is the value
/// of coefficient index `RESERVED + i`, which is exactly what
/// `BwdCoeffSetup::coefficients` and the `__constant__` symbol expect.
#[cfg(all(test, feature = "bench"))]
pub(crate) fn pseudo_bank(layer: &CoeffLayer) -> Vec<crate::primitives::field::E4> {
    use gkr_eval_isa::bwd::coeff::model::CoefficientRecipeId;
    (0..layer.coefficients.len())
        .map(|index| pseudo_coefficient(CoefficientRecipeId::from_bank_index(index)))
        .collect()
}

/// One fully realized and certified `(circuit, layer, regime, round, budget)`
/// program.
#[cfg(all(test, feature = "bench"))]
pub(crate) struct RealizedCoeffCase {
    /// The committed layout file name — the circuit's identity, spelled the same
    /// way the artifact and every census row spell it.
    pub(crate) circuit: String,
    pub(crate) layer_index: usize,
    /// The semantic IR `interpret_coeff_layer` runs.
    pub(crate) layer: CoeffLayer,
    /// The u16 stream `interpret_encoded_program` and the GPU both execute.
    pub(crate) program: EncodedProgram,
    pub(crate) binding: CoeffSourceBinding,
    pub(crate) report: ProgramReport,
    pub(crate) regime: BwdRegime,
    /// The sumcheck round this realization is bound for. Equal to
    /// `binding.target_depth`.
    pub(crate) round: u8,
    pub(crate) budget_cells: u8,
}

#[cfg(all(test, feature = "bench"))]
fn compiled_circuit_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits")
        .join(name)
}

/// The canonical `DagLayer` of one committed layout, plus its cross-layer field
/// map — the two inputs every coefficient lowering takes.
#[cfg(all(test, feature = "bench"))]
fn canonical_layer(circuit: &str, layer_index: usize) -> (DagLayer, CrossFields) {
    let layout_path = compiled_circuit_path(circuit);
    let layout_bytes = std::fs::read(&layout_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", layout_path.display()));
    let layout: crate::upstream::GKRCircuitArtifact<crate::primitives::field::BF> =
        serde_json::from_slice(&layout_bytes)
            .unwrap_or_else(|error| panic!("parse {}: {error}", layout_path.display()));
    let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("lower {circuit} DAG: {error}"));
    let cross = build_cross_layer_field_map(&dag);
    let canonical = dag
        .layers
        .get(layer_index)
        .cloned()
        .unwrap_or_else(|| panic!("{circuit} has no canonical layer {layer_index}"));
    (canonical, cross)
}

/// Realize one `(circuit, layer, regime, round)` at EVERY requested budget, with
/// the lowering, the pricing and each budget's term-order selection done once.
///
/// This is the shape Task 12's sweep needs and the shape
/// `compile_coordinate` uses: the order for budget `b` is selected at the
/// regime's own `default_target_depth` from a candidate set that includes the
/// PRECEDING budget's winner, so the whole ascending family has to be selected
/// together. Only `realize` is then re-run at `round`, which is what rebinds
/// first access and the materialization flag to the round under test.
#[cfg(all(test, feature = "bench"))]
pub(crate) fn realize_coeff_family(
    circuit: &str,
    layer_index: usize,
    canonical: &DagLayer,
    cross: &CrossFields,
    regime: BwdRegime,
    round: u8,
    budgets: &[u8],
) -> Vec<RealizedCoeffCase> {
    let label = format!("{circuit} L{layer_index} {regime:?} round {round}");
    let (layer, prices, schedule_depth) = lower_and_price(canonical, cross, regime)
        .unwrap_or_else(|error| panic!("lower {label}: {error:?}"));
    let floor_bytes = total_read_floor_bytes(&layer, &prices);

    let mut preceding: Option<Vec<gkr_eval_isa::bwd::coeff::model::TermId>> = None;
    let mut out = Vec::with_capacity(budgets.len());
    for &budget_cells in budgets {
        let budget = CellBudget::new(budget_cells).expect("legal cell budget");
        // The schedule: selected at the regime's own depth, exactly as
        // `compile_coordinate` selects it.
        let selection = select_paged_order(
            &layer,
            &prices,
            PagingRequest {
                budget,
                target_depth: schedule_depth,
            },
            preceding.as_deref(),
        )
        .unwrap_or_else(|error| panic!("select {label} c{budget_cells} order: {error:?}"));
        let order = selection.plan.order.clone();

        // ...then realized at THIS round's depth.
        let realization = realize(
            &layer,
            &prices,
            cross,
            PagingRequest {
                budget,
                target_depth: round,
            },
            &order,
            floor_bytes,
        )
        .unwrap_or_else(|error| panic!("realize {label} c{budget_cells}: {error:?}"));

        assert_eq!(
            realization.binding.target_depth, round,
            "the realization's binding must be bound for the requested round"
        );
        assert_eq!(realization.program.regime, regime);
        assert_eq!(realization.program.budget.cells(), budget_cells);

        preceding = Some(order);
        out.push(RealizedCoeffCase {
            circuit: circuit.to_owned(),
            layer_index,
            layer: layer.clone(),
            program: realization.program,
            binding: realization.binding,
            report: realization.report,
            regime,
            round,
            budget_cells,
        });
    }
    out
}

/// Realize add/sub layer 0 for one `(regime, round, budget)`.
///
/// `round` must be a legal target depth for the regime: R0 is round zero by
/// definition, and a continuation round selects the D0-D3 resolver through
/// `bwd_coeff_fold_depth`. `lower_bwd_coeff` re-checks both.
///
/// Selects this budget's order with NO preceding winner, which is what the parity
/// ladder wants: one coordinate at one budget, independent of the rest of the
/// family. Task 12's sweep uses [`realize_coeff_family`] instead, because §7.2's
/// selection is ascending-family-dependent.
#[cfg(all(test, feature = "bench"))]
pub(crate) fn load_add_sub_l0_coeff_case(
    regime: BwdRegime,
    round: u8,
    budget_cells: u8,
) -> RealizedCoeffCase {
    let (canonical, cross) = canonical_layer(ADD_SUB_LAYOUT, 0);
    realize_coeff_family(
        ADD_SUB_LAYOUT,
        0,
        &canonical,
        &cross,
        regime,
        round,
        &[budget_cells],
    )
    .pop()
    .expect("one budget realizes one case")
}

#[cfg(all(test, feature = "bench"))]
mod tests;
