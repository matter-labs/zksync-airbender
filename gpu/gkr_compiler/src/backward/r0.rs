use std::collections::HashMap;

use gkr_eval_ir::{DagCircuit, FieldKind, ReadPlace};

use super::common::distill::distill;
use super::common::interp::{interpret_lean_program, CoeffResolver, LeanInterpError};
use super::common::lean::{encode_program, validate_program, LeanCodecError, LeanProgram};
use super::common::lean_bind::{bind_lean_sources, LeanBindError, LeanSourceBinding};
use super::common::limits::{
    LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_COEFFICIENT_RECIPES, LEAN_MAX_SOURCES,
};
use super::common::lower::lower_coeff_layer;
use super::common::model::CoeffLayer;
use super::common::model::{CoeffError, NormalizedCoefficientRecipe};
use super::common::order::order_terms;
use crate::analysis::build_cross_layer_field_map;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0ProgramBundle {
    pub layers: Vec<R0LayerProgram>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0LayerProgram {
    pub layer: usize,
    pub coefficient_recipes: Vec<NormalizedCoefficientRecipe>,
    pub program: LeanProgram,
    pub binding: LeanSourceBinding,
    pub coefficients: CoeffLayer,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0CompileError {
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

impl core::fmt::Display for R0CompileError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for R0CompileError {}

fn require(
    layer: usize,
    resource: &'static str,
    required: usize,
    maximum: usize,
) -> Result<(), R0CompileError> {
    if required > maximum {
        return Err(R0CompileError::Capacity {
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
) -> Result<R0LayerProgram, R0CompileError> {
    let distilled = distill(canonical, crate::BwdRegime::R0, cross_fields);
    let coefficients =
        lower_coeff_layer(canonical, &distilled).map_err(|error| R0CompileError::Lower {
            layer: layer_index,
            error,
        })?;
    let order = order_terms(&coefficients);
    let program = encode_program(&coefficients, &order).map_err(|error| R0CompileError::Codec {
        layer: layer_index,
        error,
    })?;
    let binding = bind_lean_sources(&coefficients, cross_fields, &order).map_err(|error| {
        R0CompileError::Bind {
            layer: layer_index,
            error,
        }
    })?;
    validate_program(&program, &coefficients).map_err(|error| R0CompileError::Codec {
        layer: layer_index,
        error,
    })?;

    for (resource, required, maximum) in [
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
    Ok(R0LayerProgram {
        layer: layer_index,
        coefficient_recipes,
        program,
        binding,
        coefficients,
    })
}

pub fn compile_r0(dag: &DagCircuit) -> Result<R0ProgramBundle, R0CompileError> {
    let cross_fields = build_cross_layer_field_map(dag);
    let layers = dag
        .layers
        .iter()
        .enumerate()
        .map(|(layer, canonical)| compile_layer(layer, canonical, &cross_fields))
        .collect::<Result<_, _>>()?;
    Ok(R0ProgramBundle { layers })
}

pub fn interpret_r0_program(
    program: &R0LayerProgram,
    row: usize,
    resolver: &impl CoeffResolver,
    k: usize,
) -> Result<(super::common::Ext, super::common::Ext), LeanInterpError> {
    interpret_lean_program(&program.program, &program.coefficients, row, resolver, k)
}
