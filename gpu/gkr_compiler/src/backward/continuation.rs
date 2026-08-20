use std::collections::HashMap;

use gkr_eval_ir::{DagCircuit, FieldKind, ReadPlace};

use super::common::distill::distill;
use super::common::group::group_coeff_layer;
use super::common::interp::{interpret_lean_program, CoeffResolver, LeanInterpError};
use super::common::lean::{encode_program_atoms, validate_program, LeanCodecError, LeanProgram};
use super::common::lean_bind::{bind_lean_sources, LeanBindError, LeanSourceBinding};
use super::common::limits::{
    LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_COEFFICIENT_RECIPES, LEAN_MAX_IMMEDIATES,
    LEAN_MAX_SOURCES,
};
use super::common::lower::lower_coeff_layer;
use super::common::model::CoeffLayer;
use super::common::model::{CoeffError, CoefficientRecipeId, NormalizedCoefficientRecipe};
use super::common::order::{flatten_atoms, order_atoms};
use crate::analysis::build_cross_layer_field_map;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContinuationProgramBundle {
    pub layers: Vec<ContinuationLayerProgram>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContinuationLayerProgram {
    pub layer: usize,
    pub coefficient_recipes: Vec<NormalizedCoefficientRecipe>,
    pub c_init: Option<CoefficientRecipeId>,
    pub immediates: Vec<u32>,
    pub program: LeanProgram,
    pub binding: LeanSourceBinding,
    pub coefficients: CoeffLayer,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContinuationCompileError {
    Lower {
        layer: usize,
        error: CoeffError,
    },
    Codec {
        layer: usize,
        error: LeanCodecError,
    },
    Bind {
        layer: usize,
        error: LeanBindError,
    },
    Capacity {
        layer: usize,
        resource: &'static str,
        required: usize,
        maximum: usize,
    },
}

impl core::fmt::Display for ContinuationCompileError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for ContinuationCompileError {}

fn require(
    layer: usize,
    resource: &'static str,
    required: usize,
    maximum: usize,
) -> Result<(), ContinuationCompileError> {
    if required > maximum {
        return Err(ContinuationCompileError::Capacity {
            layer,
            resource,
            required,
            maximum,
        });
    }
    Ok(())
}

fn compile_layer(
    layer_index: usize,
    canonical: &gkr_eval_ir::DagLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
) -> Result<ContinuationLayerProgram, ContinuationCompileError> {
    let distilled = distill(canonical, crate::BwdRegime::Ext, cross_fields);
    let coefficients = lower_coeff_layer(canonical, &distilled).map_err(|error| {
        ContinuationCompileError::Lower {
            layer: layer_index,
            error,
        }
    })?;
    let coefficients =
        group_coeff_layer(coefficients).map_err(|error| ContinuationCompileError::Lower {
            layer: layer_index,
            error,
        })?;
    let atoms = order_atoms(&coefficients);
    let order = flatten_atoms(&coefficients, &atoms);
    let program = encode_program_atoms(&coefficients, &atoms).map_err(|error| {
        ContinuationCompileError::Codec {
            layer: layer_index,
            error,
        }
    })?;
    let binding = bind_lean_sources(&coefficients, cross_fields, &order).map_err(|error| {
        ContinuationCompileError::Bind {
            layer: layer_index,
            error,
        }
    })?;
    validate_program(&program, &coefficients).map_err(|error| ContinuationCompileError::Codec {
        layer: layer_index,
        error,
    })?;

    for (resource, required, maximum) in [
        (
            "immediates",
            coefficients.immediates.len(),
            LEAN_MAX_IMMEDIATES,
        ),
        (
            "coefficient_recipes",
            coefficients.coefficients.len(),
            LEAN_MAX_COEFFICIENT_RECIPES,
        ),
        ("sources", coefficients.sources.len(), LEAN_MAX_SOURCES),
        (
            "program_words",
            program.words.len(),
            LEAN_DESCRIPTOR_PROGRAM_WORDS,
        ),
    ] {
        require(layer_index, resource, required, maximum)?;
    }

    let coefficient_recipes = coefficients.coefficients.clone();
    let immediates = coefficients.immediates.clone();
    Ok(ContinuationLayerProgram {
        layer: layer_index,
        coefficient_recipes,
        c_init: coefficients.c_init,
        immediates,
        program,
        binding,
        coefficients,
    })
}

pub fn compile_continuations(
    dag: &DagCircuit,
) -> Result<ContinuationProgramBundle, ContinuationCompileError> {
    let cross_fields = build_cross_layer_field_map(dag);
    let layers = dag
        .layers
        .iter()
        .enumerate()
        .map(|(layer, canonical)| compile_layer(layer, canonical, &cross_fields))
        .collect::<Result<_, _>>()?;
    Ok(ContinuationProgramBundle { layers })
}

pub fn interpret_continuation_program(
    program: &ContinuationLayerProgram,
    row: usize,
    resolver: &impl CoeffResolver,
    k: usize,
) -> Result<(super::common::Ext, super::common::Ext), LeanInterpError> {
    interpret_lean_program(&program.program, &program.coefficients, row, resolver, k)
}
