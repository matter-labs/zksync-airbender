//! Artifact-certified backward coefficient-ISA fixtures for the GPU tests.
//!
//! One entry point, [`load_add_sub_l0_coeff_case`], which drives the PRODUCTION
//! compilation path for `add_sub_lui_auipc_mop` layer 0 and hands back everything
//! a GPU parity run needs: the semantic [`CoeffLayer`], the encoded u16 program,
//! the source binding, and the paging/placement artefacts behind them.
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
use cs::gkr_compiler::dag_ir::{lower_dag, BwdRegime, DagLayer};
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
const ADD_SUB_LAYOUT: &str = "add_sub_lui_auipc_mop_layout_gkr.json";

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

/// One fully realized and certified `(layer 0, regime, round, budget)` program.
#[cfg(all(test, feature = "bench"))]
pub(crate) struct AddSubCoeffCase {
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

/// The canonical `DagLayer` 0 of the add/sub circuit plus its cross-layer field
/// map — the two inputs every coefficient lowering takes.
#[cfg(all(test, feature = "bench"))]
fn add_sub_l0_canonical() -> (
    DagLayer,
    std::collections::HashMap<cs::gkr_compiler::dag_ir::ReadPlace, cs::gkr_compiler::dag_ir::FieldKind>,
) {
    let layout_path = compiled_circuit_path(ADD_SUB_LAYOUT);
    let layout_bytes = std::fs::read(&layout_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", layout_path.display()));
    let layout: crate::upstream::GKRCircuitArtifact<crate::primitives::field::BF> =
        serde_json::from_slice(&layout_bytes)
            .unwrap_or_else(|error| panic!("parse {}: {error}", layout_path.display()));
    let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("lower add/sub DAG: {error}"));
    let cross = build_cross_layer_field_map(&dag);
    let canonical = dag
        .layers
        .first()
        .cloned()
        .expect("add/sub artifact must have canonical layer 0");
    (canonical, cross)
}

/// Realize add/sub layer 0 for one `(regime, round, budget)`.
///
/// `round` must be a legal target depth for the regime: R0 is round zero by
/// definition, and a continuation round selects the D0-D3 resolver through
/// `bwd_coeff_fold_depth`. `lower_bwd_coeff` re-checks both.
#[cfg(all(test, feature = "bench"))]
pub(crate) fn load_add_sub_l0_coeff_case(
    regime: BwdRegime,
    round: u8,
    budget_cells: u8,
) -> AddSubCoeffCase {
    let (canonical, cross) = add_sub_l0_canonical();
    let budget = CellBudget::new(budget_cells).expect("legal cell budget");
    let (layer, prices, schedule_depth) = lower_and_price(&canonical, &cross, regime)
        .unwrap_or_else(|error| panic!("lower add/sub L0 {regime:?}: {error:?}"));
    let floor_bytes = total_read_floor_bytes(&layer, &prices);

    // The schedule: selected ONCE at the regime's own depth, the same way
    // `compile_coordinate` selects it.
    let selection = select_paged_order(
        &layer,
        &prices,
        PagingRequest {
            budget,
            target_depth: schedule_depth,
        },
        None,
    )
    .unwrap_or_else(|error| {
        panic!("select add/sub L0 {regime:?} c{budget_cells} order: {error:?}")
    });

    // ...then realized at THIS round's depth, which is what binds first access
    // and the materialization flag to the round under test.
    let realization = realize(
        &layer,
        &prices,
        &cross,
        PagingRequest {
            budget,
            target_depth: round,
        },
        &selection.plan.order,
        floor_bytes,
    )
    .unwrap_or_else(|error| {
        panic!("realize add/sub L0 {regime:?} round {round} c{budget_cells}: {error:?}")
    });

    assert_eq!(
        realization.binding.target_depth, round,
        "the realization's binding must be bound for the requested round"
    );
    assert_eq!(realization.program.regime, regime);
    assert_eq!(realization.program.budget.cells(), budget_cells);

    AddSubCoeffCase {
        layer,
        program: realization.program,
        binding: realization.binding,
        report: realization.report,
        regime,
        round,
        budget_cells,
    }
}

#[cfg(all(test, feature = "bench"))]
mod tests;
