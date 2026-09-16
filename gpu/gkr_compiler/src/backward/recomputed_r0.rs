//! MAIN R0 endpoint recomputation from input expressions. Products contribute
//! both Boolean and infinity cells; these programs require the recomputed executor.
use super::window::{
    WindowLoweringError, WINDOW_COEFFICIENT_BANK_BIAS, WINDOW_MAX_COEFFICIENT_PLANS,
};
use super::{
    CoeffLayer, CoefficientRecipeId, NormalizedCoefficientRecipe, R0CompileError,
    WindowCoefficientPlan, WindowProgram,
};
use gkr_eval_ir::{DagCircuit, FieldKind, ReadPlace};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecomputedR0Layer {
    pub layer: usize,
    pub window: WindowProgram,
    /// Index into the window coefficient bank, or None for zero.
    pub scalar_seed: Option<u16>,
    /// Quadratic terms retain C2 encoding, and the recomputed executor also
    /// evaluates their endpoint products. Linear terms read inputs, not roots.
    pub coefficients: CoeffLayer,
}

pub fn compile_recomputed_r0(dag: &DagCircuit) -> Result<Vec<RecomputedR0Layer>, R0CompileError> {
    compile_recomputed_r0_with_linear_tails(dag, false)
}

/// Whole-unit permutation; preserves coefficient bank indices.
/// Returns whether the program words or source-lane positions changed.
pub fn reorder_window_boundaries(program: &mut WindowProgram) -> bool {
    super::window::reorder_recomputed_window_boundaries(program)
}

/// Compile the input-only R0 program of every layer, optionally grouping BF
/// linear residues. One cross-layer field scan serves all layers.
pub fn compile_recomputed_r0_with_linear_tails(
    dag: &DagCircuit,
    linear_tails: bool,
) -> Result<Vec<RecomputedR0Layer>, R0CompileError> {
    let fields = crate::analysis::build_cross_layer_field_map(dag);
    (0..dag.layers.len())
        .map(|layer| compile_layer(dag, &fields, layer, linear_tails))
        .collect()
}

/// Compile one layer's input-only R0 program. Identical to the matching entry
/// of the all-layer compile; a layer index past the circuit is an error.
pub fn compile_recomputed_r0_layer(
    dag: &DagCircuit,
    layer: usize,
    linear_tails: bool,
) -> Result<RecomputedR0Layer, R0CompileError> {
    if layer >= dag.layers.len() {
        return Err(R0CompileError::UnknownLayer {
            layer,
            layers: dag.layers.len(),
        });
    }
    let fields = crate::analysis::build_cross_layer_field_map(dag);
    compile_layer(dag, &fields, layer, linear_tails)
}

/// The recipe a layer's `c_init` names: a reserved literal or a bank entry.
/// `None` when the layer has no constant term. Test oracle only.
#[cfg(test)]
fn c_init_recipe(coefficients: &CoeffLayer) -> Option<NormalizedCoefficientRecipe> {
    coefficients
        .c_init
        .and_then(|id| recipe_of(coefficients, id))
}

fn recipe_of(
    coefficients: &CoeffLayer,
    id: CoefficientRecipeId,
) -> Option<NormalizedCoefficientRecipe> {
    match id {
        CoefficientRecipeId::ONE => Some(NormalizedCoefficientRecipe::one()),
        CoefficientRecipeId::NEG_ONE => Some(NormalizedCoefficientRecipe::neg_one()),
        _ => coefficients.coefficients.get(id.bank_index()?).cloned(),
    }
}

fn compile_layer(
    dag: &DagCircuit,
    fields: &HashMap<ReadPlace, FieldKind>,
    layer: usize,
    linear_tails: bool,
) -> Result<RecomputedR0Layer, R0CompileError> {
    let canonical = dag.layers.get(layer).ok_or(R0CompileError::UnknownLayer {
        layer,
        layers: dag.layers.len(),
    })?;
    let program = super::r0::compile_layer(layer, canonical, fields, true)?;
    let mut window = super::window::lower_recomputed_window_program(&program, linear_tails)
        .map_err(|error| R0CompileError::Window { layer, error })?;
    let scalar_seed = program
        .coefficients
        .c_init
        .map(|id| scalar_seed_id(&mut window, &program.coefficients, id))
        .transpose()
        .map_err(|error| R0CompileError::Window { layer, error })?;
    Ok(RecomputedR0Layer {
        layer,
        window,
        scalar_seed,
        coefficients: program.coefficients,
    })
}

/// The scalar seed is the layer's `c_init` recipe as a `Direct` plan in the
/// window's own bank, reusing an equal plan when one exists. Bank capacity and
/// the u16 bank id are lowering errors, not panics.
fn scalar_seed_id(
    window: &mut WindowProgram,
    coefficients: &CoeffLayer,
    id: CoefficientRecipeId,
) -> Result<u16, WindowLoweringError> {
    let recipe = recipe_of(coefficients, id).ok_or_else(|| {
        WindowLoweringError::Encoding(format!("scalar seed recipe id {} is not in the bank", id.0))
    })?;
    let plan = WindowCoefficientPlan::Direct(recipe);
    let position = match window.coefficient_plans.iter().position(|p| p == &plan) {
        Some(position) => position,
        None => {
            let required = window.coefficient_plans.len() + 1;
            if required > WINDOW_MAX_COEFFICIENT_PLANS {
                return Err(WindowLoweringError::Capacity {
                    resource: "window coefficient plans with the scalar seed",
                    required,
                    capacity: WINDOW_MAX_COEFFICIENT_PLANS,
                });
            }
            window.coefficient_plans.push(plan);
            required - 1
        }
    };
    let bank_id = position + usize::from(WINDOW_COEFFICIENT_BANK_BIAS);
    u16::try_from(bank_id).map_err(|_| WindowLoweringError::Capacity {
        resource: "scalar seed bank id",
        required: bank_id,
        capacity: usize::from(u16::MAX),
    })
}

#[cfg(test)]
mod tests;
