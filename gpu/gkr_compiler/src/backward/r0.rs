use std::collections::{BTreeSet, HashMap};

use gkr_eval_ir::{DagCircuit, FieldKind, ReadPlace};

use super::common::distill::distill;
use super::common::interp::{CoeffResolver, LeanInterpError, interpret_lean_program};
use super::common::lean::{LeanCodecError, LeanProgram, encode_program, validate_program};
use super::common::lean_bind::{LeanBindError, LeanSourceBinding, bind_lean_sources_with_limits};
use super::common::lower::lower_coeff_layer;
use super::common::model::{CoeffError, CoeffLayer, ProjectionId, TermId};
use super::common::order::order_terms;
use crate::analysis::build_cross_layer_field_map;
use crate::{GpuResourceProfile, ResourceProfileError, validate_r0_profile};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0ProgramBundle {
    pub layers: Vec<R0LayerProgram>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0LayerProgram {
    pub layer: usize,
    pub coefficients: CoeffLayer,
    pub order: Vec<u32>,
    pub program: LeanProgram,
    pub binding: LeanSourceBinding,
}

impl R0LayerProgram {
    pub const fn target_depth(&self) -> u8 {
        0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0CompileError {
    Profile(ResourceProfileError),
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
    OrderCoverage {
        layer: usize,
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

fn order_covers_layer(order: &[TermId], terms: usize) -> bool {
    if order.len() != terms {
        return false;
    }
    let mut seen = vec![false; terms];
    order.iter().all(|id| match seen.get_mut(id.0 as usize) {
        Some(slot) if !*slot => {
            *slot = true;
            true
        }
        _ => false,
    })
}

fn projection_count(layer: &CoeffLayer) -> usize {
    let mut projections = BTreeSet::<ProjectionId>::new();
    for term in &layer.terms {
        term.for_each_projection_use(|projection| {
            projections.insert(projection);
        });
    }
    projections.len()
}

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
    profile: &crate::R0ResourceProfile,
) -> Result<R0LayerProgram, R0CompileError> {
    let distilled = distill(canonical, crate::BwdRegime::R0, cross_fields);
    let coefficients =
        lower_coeff_layer(canonical, &distilled).map_err(|error| R0CompileError::Lower {
            layer: layer_index,
            error,
        })?;
    let order = order_terms(&coefficients);
    if !order_covers_layer(&order, coefficients.terms.len()) {
        return Err(R0CompileError::OrderCoverage { layer: layer_index });
    }
    let program = encode_program(&coefficients, &order).map_err(|error| R0CompileError::Codec {
        layer: layer_index,
        error,
    })?;
    let binding = bind_lean_sources_with_limits(
        &coefficients,
        cross_fields,
        &order,
        0,
        profile.source_window_columns,
        profile.max_source_windows,
    )
    .map_err(|error| R0CompileError::Bind {
        layer: layer_index,
        error,
    })?;
    validate_program(&program, &coefficients).map_err(|error| R0CompileError::Codec {
        layer: layer_index,
        error,
    })?;

    for (resource, required, maximum) in [
        (
            "immediates",
            coefficients.immediates.len(),
            profile.max_immediates,
        ),
        (
            "coefficient_recipes",
            coefficients.coefficients.len(),
            profile.max_coefficient_recipes,
        ),
        ("sources", coefficients.sources.len(), profile.max_sources),
        (
            "projections",
            projection_count(&coefficients),
            profile.max_projections,
        ),
        ("records", program.words.len() / 4, profile.max_records),
        (
            "program_words",
            program.words.len(),
            profile.max_program_words,
        ),
    ] {
        require(layer_index, resource, required, maximum)?;
    }

    Ok(R0LayerProgram {
        layer: layer_index,
        coefficients,
        order: order.into_iter().map(|id| id.0).collect(),
        program,
        binding,
    })
}

pub fn compile_r0(
    dag: &DagCircuit,
    profile: &GpuResourceProfile,
) -> Result<R0ProgramBundle, R0CompileError> {
    validate_r0_profile(&profile.r0).map_err(R0CompileError::Profile)?;
    let cross_fields = build_cross_layer_field_map(dag);
    let layers = dag
        .layers
        .iter()
        .enumerate()
        .map(|(layer, canonical)| compile_layer(layer, canonical, &cross_fields, &profile.r0))
        .collect::<Result<_, _>>()?;
    Ok(R0ProgramBundle { layers })
}

pub fn interpret_r0_program(
    program: &R0LayerProgram,
    row: usize,
    resolver: &impl CoeffResolver,
    k: usize,
) -> Result<(gkr_eval_ir::Ext, gkr_eval_ir::Ext), LeanInterpError> {
    interpret_lean_program(&program.program, &program.coefficients, row, resolver, k)
}
